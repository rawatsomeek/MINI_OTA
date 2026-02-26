"""
merge_service.py — Search Result Merge & Normalization Engine
=============================================================
Version 2.0 — Enterprise OTA Platform

Responsibilities (STRICT):
  - Orchestrate parallel search across admin DB + Amadeus live inventory
  - Normalize both source schemas to a unified HotelResult structure
  - Deduplicate across sources (name + city fuzzy match)
  - Merge: live price wins for known hotels, DB hotels kept if no live match
  - Sort by dynamic pricing output (price ascending by default)
  - Return a single unified result list to the route layer

This service is the single aggregation point for all search results.
It calls InventoryService (admin DB) and AmadeusService (live).
It NEVER calculates prices — pricing is always delegated to pricing_engine.py.
It NEVER writes to DB — read-only operations only.

Search execution model:
  - Admin DB fetch:   synchronous (fast, local)
  - Amadeus fetch:    synchronous with timeout guard
  - Future:          replace with concurrent.futures.ThreadPoolExecutor
                     or asyncio.gather for true parallel execution

Deduplication algorithm:
  - Primary key: normalized hotel name (lowercase, strip common suffixes)
  - Secondary: city/region match
  - Strategy: live offer wins (replaces admin pricing with Amadeus price)
  - If live hotel not in admin DB: added as live-only entry
  - If admin hotel has no live match: kept with DB pricing
"""

from __future__ import annotations

import logging
import re
import time
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout, as_completed
from dataclasses import dataclass, field
from decimal import Decimal
from typing import Any, Dict, List, Optional, Tuple

from services.amadeus_service import (
    AmadeusService,
    NormalizedHotelOffer,
    NormalizedFlightOffer,
    AmadeusError,
    get_amadeus_service,
)
from services.inventory_service import (
    InventoryService,
    HotelRecord,
    get_inventory_service,
)

logger = logging.getLogger(__name__)


# =====================================================
# UNIFIED RESULT SCHEMAS
# =====================================================

@dataclass
class UnifiedHotelResult:
    """
    Canonical hotel result returned to routes and pricing engine.
    Merges admin DB record + optional live Amadeus offer.
    """
    # Identity
    result_id: str = ''
    source: str = 'admin'              # 'admin' | 'live' | 'merged'

    # Admin DB fields (None if live-only)
    internal_name: Optional[str] = None
    region_id: Optional[int]     = None
    hotel_type: str              = 'STANDARD'
    star_rating: int             = 3
    amenities: List[str]         = field(default_factory=list)
    images: List[str]            = field(default_factory=list)
    description: str             = ''
    sharing_capacity: int        = 2

    # Shared display fields
    hotel_name: str = ''
    city:       str = ''
    address:    str = ''
    latitude:   Optional[float] = None
    longitude:  Optional[float] = None

    # Live offer fields (None if admin-only)
    offer_id:        Optional[str]     = None
    check_in:        Optional[str]     = None
    check_out:       Optional[str]     = None
    nights:          int               = 0
    adults:          int               = 1
    room_type:       str               = ''
    board_type:      str               = ''
    live_price:      Optional[Decimal] = None
    live_currency:   str               = 'INR'
    original_price:  Optional[Decimal] = None
    original_currency: str             = 'USD'
    cancellation_policy: str           = ''

    # Admin pricing (for pricing_engine)
    admin_adult_rate_peak: Decimal = Decimal('0')
    admin_child_rate_peak: Decimal = Decimal('0')
    admin_adult_rate_off:  Decimal = Decimal('0')
    admin_child_rate_off:  Decimal = Decimal('0')
    pricing_ranges: List[Dict]     = field(default_factory=list)

    # Ranking signal
    sort_price: Decimal = Decimal('0')    # price used for sorting

    def to_dict(self) -> Dict:
        return {
            'result_id':            self.result_id,
            'source':               self.source,
            'internal_name':        self.internal_name,
            'region_id':            self.region_id,
            'hotel_type':           self.hotel_type,
            'star_rating':          self.star_rating,
            'amenities':            self.amenities,
            'images':               self.images,
            'description':          self.description,
            'sharing_capacity':     self.sharing_capacity,
            'hotel_name':           self.hotel_name,
            'city':                 self.city,
            'address':              self.address,
            'latitude':             self.latitude,
            'longitude':            self.longitude,
            'offer_id':             self.offer_id,
            'check_in':             self.check_in,
            'check_out':            self.check_out,
            'nights':               self.nights,
            'adults':               self.adults,
            'room_type':            self.room_type,
            'board_type':           self.board_type,
            'live_price':           float(self.live_price) if self.live_price else None,
            'live_currency':        self.live_currency,
            'original_price':       float(self.original_price) if self.original_price else None,
            'original_currency':    self.original_currency,
            'cancellation_policy':  self.cancellation_policy,
            'admin_adult_rate_peak': float(self.admin_adult_rate_peak),
            'admin_child_rate_peak': float(self.admin_child_rate_peak),
            'admin_adult_rate_off':  float(self.admin_adult_rate_off),
            'admin_child_rate_off':  float(self.admin_child_rate_off),
            'pricing_ranges':       self.pricing_ranges,
            'sort_price':           float(self.sort_price),
        }


@dataclass
class SearchContext:
    """Structured search parameters passed through the merge pipeline."""
    client_id:      int
    region_id:      int
    city_code:      str          # IATA city code for Amadeus
    check_in:       str          # YYYY-MM-DD
    check_out:      str          # YYYY-MM-DD
    adults:         int = 2
    children:       int = 0
    rooms:          int = 1
    star_ratings:   Optional[List[int]] = None
    max_results:    int = 30
    live_enabled:   bool = True
    live_timeout:   float = 8.0  # seconds to wait for Amadeus response
    currency:       str = 'INR'
    sort_by:        str = 'price'   # 'price' | 'rating' | 'name'
    sort_dir:       str = 'asc'     # 'asc' | 'desc'

    @property
    def nights(self) -> int:
        import datetime
        try:
            ci = datetime.date.fromisoformat(self.check_in)
            co = datetime.date.fromisoformat(self.check_out)
            return max(1, (co - ci).days)
        except Exception:
            return 1


# =====================================================
# DEDUPLICATION
# =====================================================

_STRIP_SUFFIXES = re.compile(
    r'\b(hotel|resort|inn|suites|suite|by|the|a|an|&|and)\b', re.IGNORECASE
)
_WHITESPACE = re.compile(r'\s+')


def _normalize_hotel_name(name: str) -> str:
    """
    Normalize hotel name for deduplication comparison.
    Strips common suffixes, punctuation, and whitespace.
    """
    name = name.lower().strip()
    name = re.sub(r'[^\w\s]', '', name)
    name = _STRIP_SUFFIXES.sub('', name)
    name = _WHITESPACE.sub(' ', name).strip()
    return name


def _hotels_are_same(
    name_a: str,
    name_b: str,
    city_a: str = '',
    city_b: str = '',
) -> bool:
    """
    Determine if two hotel names refer to the same property.
    Uses exact normalized match + optional city check.
    Future: replace with Levenshtein distance or embedding similarity.
    """
    norm_a = _normalize_hotel_name(name_a)
    norm_b = _normalize_hotel_name(name_b)

    if not norm_a or not norm_b:
        return False

    # Exact match after normalization
    if norm_a == norm_b:
        return True

    # Substring containment (catches "The Leela Goa" vs "Leela Goa")
    if norm_a in norm_b or norm_b in norm_a:
        if city_a and city_b:
            return city_a.lower().strip() == city_b.lower().strip()
        return True

    return False


# =====================================================
# MERGE ENGINE
# =====================================================

class MergeService:
    """
    Orchestrates search across admin DB + Amadeus live inventory,
    merges results, and returns a sorted unified list.

    Usage:
        svc = MergeService()
        ctx = SearchContext(client_id=1, region_id=1, city_code='GOI', ...)
        results = svc.search_hotels(db_conn, ctx)
    """

    def __init__(
        self,
        amadeus_service: Optional[AmadeusService] = None,
        inventory_service: Optional[InventoryService] = None,
    ):
        self._amadeus   = amadeus_service   or get_amadeus_service()
        self._inventory = inventory_service or get_inventory_service()

    # ── Main search entry point ────────────────────────────────────────────────

    def search_hotels(
        self,
        db_conn,
        ctx: SearchContext,
    ) -> Tuple[List[UnifiedHotelResult], Dict[str, Any]]:
        """
        Execute a merged hotel search.

        Returns:
            (results, meta) where:
              results: List[UnifiedHotelResult] sorted per ctx.sort_by
              meta: dict with source statistics
        """
        t0 = time.monotonic()
        meta: Dict[str, Any] = {
            'admin_hotels_found': 0,
            'live_hotels_found':  0,
            'merged_count':       0,
            'live_attempted':     ctx.live_enabled,
            'live_error':         None,
            'duration_ms':        0,
        }

        # ── 1. Fetch admin DB inventory ────────────────────────────────────────
        admin_hotels = self._inventory.get_hotels(
            db_conn,
            client_id=ctx.client_id,
            region_id=ctx.region_id,
            active_only=True,
            with_pricing_ranges=True,
        )
        meta['admin_hotels_found'] = len(admin_hotels)
        logger.info(f"MergeService: {len(admin_hotels)} admin hotels for region {ctx.region_id}")

        # ── 2. Fetch Amadeus live inventory (with timeout) ─────────────────────
        live_offers: List[NormalizedHotelOffer] = []
        if ctx.live_enabled:
            live_offers, live_err = self._fetch_live_hotels(ctx)
            meta['live_hotels_found'] = len(live_offers)
            meta['live_error']        = live_err
            if live_err:
                logger.warning(f"MergeService: live hotel error: {live_err}")

        # ── 3. Merge ───────────────────────────────────────────────────────────
        merged = self._merge_hotels(admin_hotels, live_offers, ctx)
        meta['merged_count'] = len(merged)

        # ── 4. Sort ────────────────────────────────────────────────────────────
        merged = self._sort_results(merged, ctx.sort_by, ctx.sort_dir)

        # ── 5. Limit ───────────────────────────────────────────────────────────
        merged = merged[:ctx.max_results]

        meta['duration_ms'] = int((time.monotonic() - t0) * 1000)
        return merged, meta

    def search_flights(
        self,
        ctx: SearchContext,
        origin: str,
        destination: str,
        departure_date: str,
        return_date: Optional[str] = None,
        cabin_class: str = 'ECONOMY',
    ) -> Tuple[List[NormalizedFlightOffer], Dict[str, Any]]:
        """
        Search flights via Amadeus only (no admin DB flight inventory yet).

        Returns:
            (offers, meta)
        """
        t0 = time.monotonic()
        meta: Dict[str, Any] = {
            'live_attempted': True,
            'live_error': None,
            'count': 0,
            'duration_ms': 0,
        }

        if not ctx.live_enabled:
            meta['live_error'] = 'live search disabled'
            return [], meta

        try:
            offers = self._amadeus.search_flights(
                origin=origin,
                destination=destination,
                departure_date=departure_date,
                adults=ctx.adults,
                children=ctx.children,
                cabin_class=cabin_class,
                return_date=return_date,
                currency=ctx.currency,
                max_results=ctx.max_results,
            )
            meta['count'] = len(offers)
        except AmadeusError as e:
            meta['live_error'] = str(e)
            offers = []

        meta['duration_ms'] = int((time.monotonic() - t0) * 1000)
        return offers, meta

    # ── Internal helpers ───────────────────────────────────────────────────────

    def _fetch_live_hotels(
        self,
        ctx: SearchContext,
    ) -> Tuple[List[NormalizedHotelOffer], Optional[str]]:
        """
        Fetch live hotels from Amadeus with timeout guard.
        Returns (offers, error_string_or_None).
        """
        try:
            with ThreadPoolExecutor(max_workers=1) as executor:
                future = executor.submit(
                    self._amadeus.search_hotels,
                    city_code=ctx.city_code,
                    check_in=ctx.check_in,
                    check_out=ctx.check_out,
                    adults=ctx.adults,
                    rooms=ctx.rooms,
                    ratings=ctx.star_ratings,
                    currency=ctx.currency,
                    max_results=50,
                )
                try:
                    offers = future.result(timeout=ctx.live_timeout)
                    return offers, None
                except FuturesTimeout:
                    future.cancel()
                    return [], f"Amadeus timeout after {ctx.live_timeout}s"
        except AmadeusError as e:
            return [], str(e)
        except Exception as e:
            return [], f"Unexpected live search error: {e}"

    def _merge_hotels(
        self,
        admin_hotels: List[HotelRecord],
        live_offers: List[NormalizedHotelOffer],
        ctx: SearchContext,
    ) -> List[UnifiedHotelResult]:
        """
        Merge admin DB records with live Amadeus offers.

        Merge strategy:
          1. For each admin hotel: check if a live offer matches (name similarity)
             - If match: create 'merged' result (admin metadata + live price)
             - If no match: create 'admin' result (DB pricing only)
          2. For each live offer not matched: create 'live' result (Amadeus-only)
        """
        results: List[UnifiedHotelResult] = []
        matched_offer_ids: set = set()

        # --- Pass 1: Admin hotels + live match ---
        for admin in admin_hotels:
            best_live = self._find_best_live_match(admin, live_offers, matched_offer_ids)

            if best_live:
                matched_offer_ids.add(best_live.offer_id)
                result = self._build_merged_result(admin, best_live)
            else:
                result = self._build_admin_result(admin)

            results.append(result)

        # --- Pass 2: Unmatched live offers ---
        for offer in live_offers:
            if offer.offer_id not in matched_offer_ids:
                results.append(self._build_live_result(offer, ctx))

        return results

    def _find_best_live_match(
        self,
        admin: HotelRecord,
        live_offers: List[NormalizedHotelOffer],
        already_matched: set,
    ) -> Optional[NormalizedHotelOffer]:
        """
        Find best matching live offer for an admin hotel.
        Returns the cheapest matching live offer.
        """
        candidates = [
            o for o in live_offers
            if o.offer_id not in already_matched
            and _hotels_are_same(
                admin.display_name, o.hotel_name,
                admin.city, o.city_code
            )
        ]
        if not candidates:
            return None
        # Pick cheapest matching offer
        return min(candidates, key=lambda o: o.total_price)

    @staticmethod
    def _build_merged_result(
        admin: HotelRecord,
        live: NormalizedHotelOffer,
    ) -> UnifiedHotelResult:
        """Admin metadata + live Amadeus pricing."""
        return UnifiedHotelResult(
            result_id=f"merged_{admin.internal_name}_{live.offer_id}",
            source='merged',
            internal_name=admin.internal_name,
            region_id=admin.region_id,
            hotel_type=admin.hotel_type,
            star_rating=max(admin.star_rating, live.star_rating),
            amenities=admin.amenities or live.amenities,
            images=admin.images,
            description=admin.description,
            sharing_capacity=admin.sharing_capacity,
            hotel_name=admin.display_name,
            city=admin.city or live.city_code,
            address=admin.address,
            latitude=live.latitude or None,
            longitude=live.longitude or None,
            offer_id=live.offer_id,
            check_in=live.check_in,
            check_out=live.check_out,
            nights=live.nights,
            adults=live.adults,
            room_type=live.room_type,
            board_type=live.board_type,
            live_price=live.total_price,
            live_currency=live.currency,
            original_price=live.original_price,
            original_currency=live.original_currency,
            cancellation_policy=live.cancellation_policy,
            admin_adult_rate_peak=admin.adult_rate_peak,
            admin_child_rate_peak=admin.child_rate_peak,
            admin_adult_rate_off=admin.adult_rate_off,
            admin_child_rate_off=admin.child_rate_off,
            pricing_ranges=admin.pricing_ranges,
            sort_price=live.total_price,
        )

    @staticmethod
    def _build_admin_result(admin: HotelRecord) -> UnifiedHotelResult:
        """Admin-only result — no live match."""
        # Use peak rate as sort signal (rough estimate)
        sort_price = admin.adult_rate_peak * 2 if admin.adult_rate_peak else Decimal('9999999')
        return UnifiedHotelResult(
            result_id=f"admin_{admin.internal_name}",
            source='admin',
            internal_name=admin.internal_name,
            region_id=admin.region_id,
            hotel_type=admin.hotel_type,
            star_rating=admin.star_rating,
            amenities=admin.amenities,
            images=admin.images,
            description=admin.description,
            sharing_capacity=admin.sharing_capacity,
            hotel_name=admin.display_name,
            city=admin.city,
            address=admin.address,
            admin_adult_rate_peak=admin.adult_rate_peak,
            admin_child_rate_peak=admin.child_rate_peak,
            admin_adult_rate_off=admin.adult_rate_off,
            admin_child_rate_off=admin.child_rate_off,
            pricing_ranges=admin.pricing_ranges,
            sort_price=sort_price,
        )

    @staticmethod
    def _build_live_result(
        live: NormalizedHotelOffer,
        ctx: SearchContext,
    ) -> UnifiedHotelResult:
        """Live-only result — no admin match."""
        return UnifiedHotelResult(
            result_id=f"live_{live.offer_id}",
            source='live',
            hotel_name=live.hotel_name,
            city=live.city_code,
            star_rating=live.star_rating,
            amenities=live.amenities,
            latitude=live.latitude,
            longitude=live.longitude,
            offer_id=live.offer_id,
            check_in=live.check_in,
            check_out=live.check_out,
            nights=live.nights,
            adults=live.adults,
            room_type=live.room_type,
            board_type=live.board_type,
            live_price=live.total_price,
            live_currency=live.currency,
            original_price=live.original_price,
            original_currency=live.original_currency,
            cancellation_policy=live.cancellation_policy,
            sort_price=live.total_price,
        )

    @staticmethod
    def _sort_results(
        results: List[UnifiedHotelResult],
        sort_by: str,
        sort_dir: str,
    ) -> List[UnifiedHotelResult]:
        """Sort unified results by specified field."""
        reverse = sort_dir.lower() == 'desc'

        if sort_by == 'price':
            results.sort(key=lambda r: r.sort_price, reverse=reverse)
        elif sort_by == 'rating':
            results.sort(key=lambda r: r.star_rating, reverse=not reverse)
        elif sort_by == 'name':
            results.sort(key=lambda r: r.hotel_name.lower(), reverse=reverse)
        else:
            results.sort(key=lambda r: r.sort_price, reverse=reverse)

        return results


# =====================================================
# SINGLETON
# =====================================================

_merge_service: Optional[MergeService] = None


def get_merge_service() -> MergeService:
    """Return singleton MergeService instance."""
    global _merge_service
    if _merge_service is None:
        _merge_service = MergeService()
    return _merge_service