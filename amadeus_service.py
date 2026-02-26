"""
amadeus_service.py — Amadeus GDS Integration Layer
====================================================
Version 2.0 — Enterprise OTA Platform

Responsibilities (STRICT):
  - Token lifecycle management (auto-refresh with expiry buffer)
  - Hotel search by city (by-city, hotel-ids, hotel-offers)
  - Flight offer search (one-way + return)
  - Offer price confirmation before booking
  - Flight + Hotel order creation (PNR generation)
  - Raw offer caching (in-memory, Redis-ready interface)
  - Response normalization to internal schema
  - Retry logic with exponential backoff
  - Structured error hierarchy

This service NEVER calculates prices.
It returns raw + normalized data structures only.
Pricing decisions remain in pricing_engine.py.

Integration pattern:
  - merge_service.py calls AmadeusService to fetch live inventory
  - app.py routes call merge_service, NOT this service directly
  - booking routes call AmadeusService.create_flight_order() / create_hotel_order()

Scalability notes:
  - Token store is pluggable (default: in-memory, swap to Redis)
  - HTTP client uses connection pooling via requests.Session
  - All Amadeus calls pass through _request() → uniform retry + logging
  - Future: replace requests.Session with httpx.AsyncClient for async support
"""

from __future__ import annotations

import os
import time
import uuid
import logging
import threading
from decimal import Decimal
from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass, field

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logger = logging.getLogger(__name__)


# =====================================================
# EXCEPTIONS
# =====================================================

class AmadeusError(Exception):
    """Base Amadeus service error."""

class AmadeusAuthError(AmadeusError):
    """Authentication / token failure."""

class AmadeusRateLimitError(AmadeusError):
    """429 – rate limit hit."""

class AmadeusNotFoundError(AmadeusError):
    """No results / resource not found."""

class AmadeusOfferExpiredError(AmadeusError):
    """Cached offer no longer valid for booking."""

class AmadeusBookingError(AmadeusError):
    """Order creation failure."""


# =====================================================
# TOKEN STORE — pluggable interface
# =====================================================

class _InMemoryTokenStore:
    """
    Thread-safe in-memory token store.
    Replace this class with a Redis-backed implementation
    in a multi-worker / multi-process deployment.
    """
    def __init__(self):
        self._token: Optional[str] = None
        self._expires_at: float = 0.0
        self._lock = threading.Lock()

    def get(self) -> Optional[str]:
        with self._lock:
            if self._token and time.time() < self._expires_at:
                return self._token
        return None

    def set(self, token: str, expires_in: int, buffer_seconds: int = 60) -> None:
        with self._lock:
            self._token = token
            self._expires_at = time.time() + expires_in - buffer_seconds

    def invalidate(self) -> None:
        with self._lock:
            self._token = None
            self._expires_at = 0.0


# =====================================================
# OFFER CACHE — pluggable interface
# =====================================================

@dataclass
class _CachedOffer:
    offer_id: str
    raw: Dict[str, Any]
    offer_type: str          # 'flight' | 'hotel'
    expires_at: float

class _InMemoryOfferCache:
    """
    Thread-safe in-memory offer cache.
    Replace with Redis in production multi-worker setup.
    """
    TTL_SECONDS = int(os.environ.get('OFFER_CACHE_TTL', '3600'))

    def __init__(self):
        self._store: Dict[str, _CachedOffer] = {}
        self._lock = threading.Lock()

    def put(self, offer_id: str, raw: Dict, offer_type: str) -> None:
        with self._lock:
            self._store[offer_id] = _CachedOffer(
                offer_id=offer_id,
                raw=raw,
                offer_type=offer_type,
                expires_at=time.time() + self.TTL_SECONDS,
            )

    def get(self, offer_id: str) -> Optional[_CachedOffer]:
        with self._lock:
            entry = self._store.get(offer_id)
            if entry and time.time() < entry.expires_at:
                return entry
            if entry:
                del self._store[offer_id]
        return None

    def purge_expired(self) -> int:
        now = time.time()
        with self._lock:
            expired = [k for k, v in self._store.items() if now >= v.expires_at]
            for k in expired:
                del self._store[k]
        return len(expired)


# =====================================================
# NORMALIZED RESULT SCHEMAS
# =====================================================

@dataclass
class NormalizedHotelOffer:
    """Canonical hotel offer structure used across the platform."""
    source: str = 'amadeus'
    offer_id: str = ''
    hotel_id: str = ''
    hotel_name: str = ''
    chain_code: str = ''
    city_code: str = ''
    star_rating: int = 0
    room_type: str = ''
    board_type: str = ''
    check_in: str = ''
    check_out: str = ''
    nights: int = 0
    adults: int = 1
    total_price: Decimal = Decimal('0')
    currency: str = 'INR'
    original_price: Decimal = Decimal('0')
    original_currency: str = 'USD'
    cancellation_policy: str = ''
    amenities: List[str] = field(default_factory=list)
    images: List[str] = field(default_factory=list)
    latitude: Optional[float] = None
    longitude: Optional[float] = None
    raw: Dict = field(default_factory=dict)

    def to_dict(self) -> Dict:
        return {
            'source': self.source,
            'offer_id': self.offer_id,
            'hotel_id': self.hotel_id,
            'hotel_name': self.hotel_name,
            'chain_code': self.chain_code,
            'city_code': self.city_code,
            'star_rating': self.star_rating,
            'room_type': self.room_type,
            'board_type': self.board_type,
            'check_in': self.check_in,
            'check_out': self.check_out,
            'nights': self.nights,
            'adults': self.adults,
            'total_price': float(self.total_price),
            'currency': self.currency,
            'original_price': float(self.original_price),
            'original_currency': self.original_currency,
            'cancellation_policy': self.cancellation_policy,
            'amenities': self.amenities,
            'images': self.images,
            'latitude': self.latitude,
            'longitude': self.longitude,
        }


@dataclass
class NormalizedFlightOffer:
    """Canonical flight offer structure used across the platform."""
    source: str = 'amadeus'
    offer_id: str = ''
    airline: str = ''
    airline_name: str = ''
    flight_number: str = ''
    origin: str = ''
    destination: str = ''
    departure_time: str = ''
    arrival_time: str = ''
    duration: str = ''
    stops: int = 0
    cabin_class: str = 'ECONOMY'
    return_departure: str = ''
    return_arrival: str = ''
    is_return: bool = False
    price_per_adult: Decimal = Decimal('0')
    total_price: Decimal = Decimal('0')
    currency: str = 'INR'
    seats_available: int = 0
    raw: Dict = field(default_factory=dict)

    def to_dict(self) -> Dict:
        return {
            'source': self.source,
            'offer_id': self.offer_id,
            'airline': self.airline,
            'airline_name': self.airline_name,
            'flight_number': self.flight_number,
            'origin': self.origin,
            'destination': self.destination,
            'departure_time': self.departure_time,
            'arrival_time': self.arrival_time,
            'duration': self.duration,
            'stops': self.stops,
            'cabin_class': self.cabin_class,
            'return_departure': self.return_departure,
            'return_arrival': self.return_arrival,
            'is_return': self.is_return,
            'price_per_adult': float(self.price_per_adult),
            'total_price': float(self.total_price),
            'currency': self.currency,
            'seats_available': self.seats_available,
        }


# =====================================================
# CURRENCY CONVERTER (stub — replace with live FX service)
# =====================================================

class _CurrencyConverter:
    """
    Stub currency converter.
    Replace with a live FX feed (ECB, Open Exchange Rates, etc.)
    or a separate FX microservice in production.
    """
    # Hard-coded fallback rates (USD → target). Update via env or DB.
    _FALLBACK_RATES: Dict[str, float] = {
        'INR': float(os.environ.get('FX_USD_INR', '83.5')),
        'EUR': float(os.environ.get('FX_USD_EUR', '0.92')),
        'GBP': float(os.environ.get('FX_USD_GBP', '0.79')),
        'USD': 1.0,
    }

    def convert(self, amount: Decimal, from_currency: str, to_currency: str) -> Decimal:
        if from_currency == to_currency:
            return amount
        try:
            rate_from = self._FALLBACK_RATES.get(from_currency, 1.0)
            rate_to   = self._FALLBACK_RATES.get(to_currency, 1.0)
            return (amount / Decimal(str(rate_from))) * Decimal(str(rate_to))
        except Exception as e:
            logger.warning(f"Currency conversion failed {from_currency}→{to_currency}: {e}")
            return amount


# =====================================================
# AMADEUS SERVICE
# =====================================================

class AmadeusService:
    """
    Amadeus GDS integration service.

    Usage:
        svc = AmadeusService()
        hotels = svc.search_hotels(city_code='GOI', check_in='2025-12-01',
                                    check_out='2025-12-05', adults=2)
        flights = svc.search_flights(origin='DEL', destination='GOI',
                                      departure_date='2025-12-01', adults=2)
    """

    # Amadeus API base URLs
    _PROD_BASE  = 'https://api.amadeus.com'
    _TEST_BASE  = 'https://test.api.amadeus.com'

    # Endpoints
    _TOKEN_PATH         = '/v1/security/oauth2/token'
    _HOTEL_BY_CITY      = '/v1/reference-data/locations/hotels/by-city'
    _HOTEL_OFFERS       = '/v3/shopping/hotel-offers'
    _HOTEL_OFFER_PRICE  = '/v3/shopping/hotel-offers/{offer_id}'
    _FLIGHT_OFFERS      = '/v2/shopping/flight-offers'
    _FLIGHT_PRICE       = '/v1/shopping/flight-offers/pricing'
    _FLIGHT_ORDER       = '/v1/booking/flight-orders'
    _HOTEL_ORDER        = '/v2/booking/hotel-orders'

    # Supported cabin classes
    CABIN_CLASSES = ('ECONOMY', 'PREMIUM_ECONOMY', 'BUSINESS', 'FIRST')

    def __init__(
        self,
        client_id: Optional[str] = None,
        client_secret: Optional[str] = None,
        test_mode: Optional[bool] = None,
        token_store: Optional[_InMemoryTokenStore] = None,
        offer_cache: Optional[_InMemoryOfferCache] = None,
        currency_converter: Optional[_CurrencyConverter] = None,
        target_currency: str = 'INR',
    ):
        self.client_id     = client_id     or os.environ.get('AMADEUS_CLIENT_ID', '')
        self.client_secret = client_secret or os.environ.get('AMADEUS_CLIENT_SECRET', '')
        self.test_mode     = test_mode if test_mode is not None else (
            os.environ.get('AMADEUS_ENV', 'test').lower() != 'production'
        )
        self.base_url      = self._TEST_BASE if self.test_mode else self._PROD_BASE
        self.target_currency = target_currency

        self._token_store = token_store or _InMemoryTokenStore()
        self._offer_cache = offer_cache or _InMemoryOfferCache()
        self._fx          = currency_converter or _CurrencyConverter()

        # Connection-pooled HTTP session with retry
        self._session = self._build_session()

        logger.info(
            f"AmadeusService initialized | env={'TEST' if self.test_mode else 'PRODUCTION'} "
            f"| base={self.base_url} | target_currency={self.target_currency}"
        )

    # ── Session builder ────────────────────────────────────────────────────────

    @staticmethod
    def _build_session() -> requests.Session:
        session = requests.Session()
        retry = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[500, 502, 503, 504],
            allowed_methods=['GET', 'POST'],
        )
        adapter = HTTPAdapter(
            max_retries=retry,
            pool_connections=10,
            pool_maxsize=20,
        )
        session.mount('https://', adapter)
        return session

    # ── Token management ───────────────────────────────────────────────────────

    def _get_token(self) -> str:
        """Return a valid OAuth2 bearer token, refreshing if needed."""
        cached = self._token_store.get()
        if cached:
            return cached

        if not self.client_id or not self.client_secret:
            raise AmadeusAuthError(
                "AMADEUS_CLIENT_ID and AMADEUS_CLIENT_SECRET must be set."
            )

        resp = self._session.post(
            f"{self.base_url}{self._TOKEN_PATH}",
            data={
                'grant_type': 'client_credentials',
                'client_id': self.client_id,
                'client_secret': self.client_secret,
            },
            timeout=15,
        )

        if resp.status_code == 401:
            raise AmadeusAuthError("Invalid Amadeus credentials.")
        if not resp.ok:
            raise AmadeusAuthError(
                f"Token request failed: {resp.status_code} — {resp.text[:200]}"
            )

        data = resp.json()
        token = data.get('access_token', '')
        expires_in = int(data.get('expires_in', 1799))

        self._token_store.set(token, expires_in)
        logger.debug("Amadeus token refreshed.")
        return token

    # ── Core HTTP wrapper ──────────────────────────────────────────────────────

    def _request(
        self,
        method: str,
        path: str,
        params: Optional[Dict] = None,
        json_body: Optional[Dict] = None,
        timeout: int = 30,
        _retry_auth: bool = True,
    ) -> Dict:
        """
        Centralized HTTP wrapper for all Amadeus calls.
        Handles auth, error mapping, and structured logging.
        """
        token = self._get_token()
        headers = {
            'Authorization': f'Bearer {token}',
            'Content-Type': 'application/json',
        }
        url = f"{self.base_url}{path}"

        try:
            resp = self._session.request(
                method=method.upper(),
                url=url,
                headers=headers,
                params=params,
                json=json_body,
                timeout=timeout,
            )
        except requests.Timeout:
            raise AmadeusError(f"Amadeus API timeout: {method} {path}")
        except requests.ConnectionError as e:
            raise AmadeusError(f"Amadeus API connection error: {e}")

        # Handle 401 → refresh token once
        if resp.status_code == 401 and _retry_auth:
            self._token_store.invalidate()
            return self._request(method, path, params, json_body, timeout, _retry_auth=False)

        if resp.status_code == 429:
            raise AmadeusRateLimitError("Amadeus rate limit exceeded.")

        if resp.status_code == 404:
            raise AmadeusNotFoundError(f"Amadeus resource not found: {path}")

        if not resp.ok:
            try:
                err_body = resp.json()
            except Exception:
                err_body = resp.text[:300]
            raise AmadeusError(
                f"Amadeus {method} {path} → {resp.status_code}: {err_body}"
            )

        return resp.json()

    # ── Hotel search ───────────────────────────────────────────────────────────

    def _fetch_hotel_ids_for_city(
        self,
        city_code: str,
        ratings: Optional[List[int]] = None,
        max_hotels: int = 50,
    ) -> List[str]:
        """
        Step 1: Resolve hotel IDs for a city code.
        Ratings: [3,4,5] → server-side star filter.
        """
        params: Dict[str, Any] = {
            'cityCode': city_code.upper(),
            'hotelSource': 'ALL',
        }
        if ratings:
            params['ratings'] = ','.join(str(r) for r in ratings)

        try:
            data = self._request('GET', self._HOTEL_BY_CITY, params=params)
        except AmadeusNotFoundError:
            return []

        hotels = data.get('data', [])[:max_hotels]

        # Secondary validation: ensure returned hotels match requested ratings
        if ratings:
            rating_set = set(str(r) for r in ratings)
            hotels = [
                h for h in hotels
                if str(h.get('rating', '')) in rating_set or not h.get('rating')
            ]

        return [h['hotelId'] for h in hotels if h.get('hotelId')]

    def search_hotels(
        self,
        city_code: str,
        check_in: str,
        check_out: str,
        adults: int = 2,
        rooms: int = 1,
        ratings: Optional[List[int]] = None,
        currency: Optional[str] = None,
        max_results: int = 20,
    ) -> List[NormalizedHotelOffer]:
        """
        Full hotel search pipeline:
          1. Resolve hotel IDs for city
          2. Fetch hotel offers (batched)
          3. Normalize + convert currency
          4. Cache raw offers by offer_id
          5. Return sorted by price

        Args:
            city_code:   IATA city code (e.g. 'GOI' for Goa)
            check_in:    ISO date string (YYYY-MM-DD)
            check_out:   ISO date string (YYYY-MM-DD)
            adults:      Number of adult guests
            rooms:       Number of rooms
            ratings:     Star ratings filter e.g. [3,4,5]
            currency:    Response currency (defaults to target_currency)
            max_results: Max offers to return

        Returns:
            List of NormalizedHotelOffer sorted by price ascending.
        """
        target_currency = currency or self.target_currency

        hotel_ids = self._fetch_hotel_ids_for_city(city_code, ratings, max_hotels=100)
        if not hotel_ids:
            logger.info(f"No hotel IDs found for city {city_code}")
            return []

        # Amadeus accepts max 100 hotel IDs per request
        offers: List[NormalizedHotelOffer] = []

        for batch_start in range(0, len(hotel_ids), 100):
            batch = hotel_ids[batch_start:batch_start + 100]
            params = {
                'hotelIds': ','.join(batch),
                'checkInDate': check_in,
                'checkOutDate': check_out,
                'adults': adults,
                'roomQuantity': rooms,
                'currency': target_currency,
                'bestRateOnly': 'true',
                'includedData': 'POLICY_DETAILS,LOYALTY,ROOM_FACILITIES',
            }

            try:
                data = self._request('GET', self._HOTEL_OFFERS, params=params)
            except (AmadeusNotFoundError, AmadeusError) as e:
                logger.warning(f"Hotel offers batch error for {city_code}: {e}")
                continue

            for raw_hotel in data.get('data', []):
                try:
                    normalized = self._normalize_hotel_offer(
                        raw_hotel, check_in, check_out, adults, target_currency
                    )
                    # Cache raw offer for booking
                    self._offer_cache.put(
                        normalized.offer_id, raw_hotel, 'hotel'
                    )
                    offers.append(normalized)
                except Exception as e:
                    logger.debug(f"Hotel normalization error: {e}")

            if len(offers) >= max_results:
                break

        offers.sort(key=lambda o: o.total_price)
        return offers[:max_results]

    def _normalize_hotel_offer(
        self,
        raw: Dict,
        check_in: str,
        check_out: str,
        adults: int,
        target_currency: str,
    ) -> NormalizedHotelOffer:
        """Transform raw Amadeus hotel offer to NormalizedHotelOffer."""
        hotel_data = raw.get('hotel', {})
        offers_list = raw.get('offers', [{}])
        offer = offers_list[0] if offers_list else {}

        offer_id = offer.get('id', str(uuid.uuid4()))
        room_type = offer.get('room', {}).get('type', '')
        board_type = offer.get('boardType', 'ROOM_ONLY')

        # Price
        price_info = offer.get('price', {})
        raw_total    = Decimal(str(price_info.get('total', '0')))
        raw_currency = price_info.get('currency', 'USD')

        converted_total = self._fx.convert(raw_total, raw_currency, target_currency)

        # Dates / nights
        import datetime as dt
        try:
            ci = dt.date.fromisoformat(check_in)
            co = dt.date.fromisoformat(check_out)
            nights = max(1, (co - ci).days)
        except Exception:
            nights = 1

        # Amenities
        amenities = [
            a.get('description', {}).get('text', '')
            for a in hotel_data.get('amenities', [])
            if isinstance(a, dict)
        ][:10]

        # Cancellation policy
        cancel_policy = ''
        policies = offer.get('policies', {}).get('cancellations', [])
        if policies:
            cancel_policy = policies[0].get('description', {}).get('text', 'Non-refundable')

        # Coordinates
        lat = hotel_data.get('latitude')
        lon = hotel_data.get('longitude')

        return NormalizedHotelOffer(
            source='amadeus',
            offer_id=offer_id,
            hotel_id=hotel_data.get('hotelId', ''),
            hotel_name=hotel_data.get('name', 'Unknown Hotel'),
            chain_code=hotel_data.get('chainCode', ''),
            city_code=hotel_data.get('cityCode', ''),
            star_rating=int(hotel_data.get('rating', 0) or 0),
            room_type=room_type,
            board_type=board_type,
            check_in=check_in,
            check_out=check_out,
            nights=nights,
            adults=adults,
            total_price=converted_total,
            currency=target_currency,
            original_price=raw_total,
            original_currency=raw_currency,
            cancellation_policy=cancel_policy,
            amenities=amenities,
            latitude=float(lat) if lat else None,
            longitude=float(lon) if lon else None,
            raw=raw,
        )

    # ── Flight search ──────────────────────────────────────────────────────────

    def search_flights(
        self,
        origin: str,
        destination: str,
        departure_date: str,
        adults: int = 1,
        children: int = 0,
        infants: int = 0,
        cabin_class: str = 'ECONOMY',
        return_date: Optional[str] = None,
        currency: Optional[str] = None,
        max_results: int = 10,
        non_stop: bool = False,
    ) -> List[NormalizedFlightOffer]:
        """
        Search Amadeus for flight offers.

        Args:
            origin:         IATA airport code (e.g. 'DEL')
            destination:    IATA airport code (e.g. 'GOI')
            departure_date: ISO date (YYYY-MM-DD)
            adults:         Adult passenger count
            children:       Child passenger count (2-11 years)
            infants:        Infant count (under 2)
            cabin_class:    ECONOMY | PREMIUM_ECONOMY | BUSINESS | FIRST
            return_date:    For round-trip; None = one-way
            currency:       Response currency
            max_results:    Max offers to return
            non_stop:       Filter to non-stop flights only

        Returns:
            List of NormalizedFlightOffer sorted by price ascending.
        """
        if cabin_class not in self.CABIN_CLASSES:
            cabin_class = 'ECONOMY'

        target_currency = currency or self.target_currency

        params: Dict[str, Any] = {
            'originLocationCode': origin.upper(),
            'destinationLocationCode': destination.upper(),
            'departureDate': departure_date,
            'adults': adults,
            'currencyCode': target_currency,
            'max': max_results,
            'travelClass': cabin_class,
        }
        if children:
            params['children'] = children
        if infants:
            params['infants'] = infants
        if return_date:
            params['returnDate'] = return_date
        if non_stop:
            params['nonStop'] = 'true'

        try:
            data = self._request('GET', self._FLIGHT_OFFERS, params=params)
        except AmadeusNotFoundError:
            return []

        dictionaries = data.get('dictionaries', {})
        carriers      = dictionaries.get('carriers', {})
        aircraft      = dictionaries.get('aircraft', {})

        offers: List[NormalizedFlightOffer] = []
        for raw_offer in data.get('data', []):
            try:
                normalized = self._normalize_flight_offer(
                    raw_offer, carriers, return_date, target_currency
                )
                self._offer_cache.put(normalized.offer_id, raw_offer, 'flight')
                offers.append(normalized)
            except Exception as e:
                logger.debug(f"Flight normalization error: {e}")

        offers.sort(key=lambda o: o.total_price)
        return offers

    def _normalize_flight_offer(
        self,
        raw: Dict,
        carriers: Dict,
        return_date: Optional[str],
        target_currency: str,
    ) -> NormalizedFlightOffer:
        """Transform raw Amadeus flight offer to NormalizedFlightOffer."""
        offer_id = raw.get('id', str(uuid.uuid4()))
        itineraries = raw.get('itineraries', [])

        # Outbound leg
        out_itin = itineraries[0] if itineraries else {}
        out_segs = out_itin.get('segments', [])
        first_seg = out_segs[0] if out_segs else {}
        last_seg  = out_segs[-1] if out_segs else {}

        carrier_code = first_seg.get('carrierCode', '')
        airline_name = carriers.get(carrier_code, carrier_code)
        flight_number = f"{carrier_code}{first_seg.get('number', '')}"

        departure_time = first_seg.get('departure', {}).get('at', '')
        arrival_time   = last_seg.get('arrival', {}).get('at', '')
        duration       = out_itin.get('duration', '')
        stops          = max(0, len(out_segs) - 1)

        # Return leg
        return_departure = ''
        return_arrival   = ''
        is_return        = bool(return_date and len(itineraries) > 1)
        if is_return:
            ret_itin = itineraries[1]
            ret_segs = ret_itin.get('segments', [])
            if ret_segs:
                return_departure = ret_segs[0].get('departure', {}).get('at', '')
                return_arrival   = ret_segs[-1].get('arrival', {}).get('at', '')

        # Price
        price_info  = raw.get('price', {})
        raw_total   = Decimal(str(price_info.get('grandTotal', '0')))
        raw_curr    = price_info.get('currency', 'USD')
        conv_total  = self._fx.convert(raw_total, raw_curr, target_currency)

        # Price per adult
        traveler_prices = raw.get('travelerPricings', [])
        adult_pricing   = next(
            (tp for tp in traveler_prices if tp.get('travelerType') == 'ADULT'), {}
        )
        raw_adult_price = Decimal(
            str(adult_pricing.get('price', {}).get('total', str(raw_total)))
        )
        conv_adult = self._fx.convert(raw_adult_price, raw_curr, target_currency)

        # Seats
        seats = raw.get('numberOfBookableSeats', 0)

        # Cabin
        cabin = 'ECONOMY'
        if traveler_prices:
            segments = traveler_prices[0].get('fareDetailsBySegment', [])
            if segments:
                cabin = segments[0].get('cabin', 'ECONOMY')

        return NormalizedFlightOffer(
            source='amadeus',
            offer_id=offer_id,
            airline=carrier_code,
            airline_name=airline_name,
            flight_number=flight_number,
            origin=first_seg.get('departure', {}).get('iataCode', ''),
            destination=last_seg.get('arrival', {}).get('iataCode', ''),
            departure_time=departure_time,
            arrival_time=arrival_time,
            duration=duration,
            stops=stops,
            cabin_class=cabin,
            return_departure=return_departure,
            return_arrival=return_arrival,
            is_return=is_return,
            price_per_adult=conv_adult,
            total_price=conv_total,
            currency=target_currency,
            seats_available=int(seats),
            raw=raw,
        )

    # ── Offer price confirmation ───────────────────────────────────────────────

    def confirm_flight_price(self, offer_id: str) -> Dict:
        """
        Confirm real-time price of a cached flight offer before booking.
        Returns updated price confirmation or raises AmadeusOfferExpiredError.
        """
        cached = self._offer_cache.get(offer_id)
        if not cached or cached.offer_type != 'flight':
            raise AmadeusOfferExpiredError(
                f"Flight offer {offer_id} not found in cache or expired."
            )

        data = self._request(
            'POST',
            self._FLIGHT_PRICE,
            json_body={'data': {'type': 'flight-offers-pricing', 'flightOffers': [cached.raw]}},
        )
        return data

    def confirm_hotel_price(self, offer_id: str) -> Dict:
        """
        Confirm real-time availability and price of a cached hotel offer.
        """
        path = self._HOTEL_OFFER_PRICE.format(offer_id=offer_id)
        try:
            data = self._request('GET', path)
            return data
        except AmadeusNotFoundError:
            raise AmadeusOfferExpiredError(
                f"Hotel offer {offer_id} is no longer available."
            )

    # ── Order creation ─────────────────────────────────────────────────────────

    def create_flight_order(
        self,
        offer_id: str,
        travelers: List[Dict],
        contact: Dict,
    ) -> Dict:
        """
        Create a real Amadeus flight order (PNR generation).

        Args:
            offer_id:  Internal offer_id from cache
            travelers: List of traveler dicts (name, DOB, passport, etc.)
            contact:   Contact info dict (email, phone)

        Returns:
            Raw Amadeus order response containing PNR reference.

        Raises:
            AmadeusOfferExpiredError: Offer not in cache.
            AmadeusBookingError: Order creation failed.
        """
        cached = self._offer_cache.get(offer_id)
        if not cached or cached.offer_type != 'flight':
            raise AmadeusOfferExpiredError(f"Flight offer {offer_id} expired.")

        # Re-price before booking
        try:
            priced = self.confirm_flight_price(offer_id)
            priced_offer = priced.get('data', {}).get('flightOffers', [cached.raw])[0]
        except AmadeusOfferExpiredError:
            raise
        except Exception as e:
            logger.warning(f"Flight re-pricing failed, using cached offer: {e}")
            priced_offer = cached.raw

        payload = {
            'data': {
                'type': 'flight-order',
                'flightOffers': [priced_offer],
                'travelers': travelers,
                'contacts': [contact],
                'remarks': {'general': [{'subType': 'GENERAL_MISCELLANEOUS', 'text': 'OTA BOOKING'}]},
            }
        }

        try:
            result = self._request('POST', self._FLIGHT_ORDER, json_body=payload, timeout=45)
        except AmadeusError as e:
            raise AmadeusBookingError(f"Flight order creation failed: {e}")

        return result

    def create_hotel_order(
        self,
        offer_id: str,
        guests: List[Dict],
        payment: Dict,
    ) -> Dict:
        """
        Create a real Amadeus hotel order (confirmation number generation).

        Args:
            offer_id: Internal offer_id from cache
            guests:   List of guest dicts
            payment:  Payment method dict (method, card details if required)

        Returns:
            Raw Amadeus hotel order response.

        Raises:
            AmadeusOfferExpiredError: Offer not in cache.
            AmadeusBookingError: Order creation failed.
        """
        cached = self._offer_cache.get(offer_id)
        if not cached or cached.offer_type != 'hotel':
            raise AmadeusOfferExpiredError(f"Hotel offer {offer_id} expired.")

        hotel_offers = cached.raw.get('offers', [])
        if not hotel_offers:
            raise AmadeusBookingError("No hotel offers in cached data.")

        payload = {
            'data': {
                'offerId': offer_id,
                'guests': guests,
                'payments': [payment],
            }
        }

        try:
            result = self._request('POST', self._HOTEL_ORDER, json_body=payload, timeout=45)
        except AmadeusError as e:
            raise AmadeusBookingError(f"Hotel order creation failed: {e}")

        return result

    # ── Utility ────────────────────────────────────────────────────────────────

    def health_check(self) -> Dict[str, Any]:
        """
        Verify Amadeus connectivity by fetching a token.
        Returns health status dict.
        """
        try:
            self._get_token()
            return {
                'status': 'ok',
                'env': 'test' if self.test_mode else 'production',
                'base_url': self.base_url,
            }
        except AmadeusAuthError as e:
            return {'status': 'auth_error', 'detail': str(e)}
        except Exception as e:
            return {'status': 'error', 'detail': str(e)}

    def purge_offer_cache(self) -> int:
        """Purge expired entries from offer cache. Returns count purged."""
        return self._offer_cache.purge_expired()


# =====================================================
# SINGLETON FACTORY
# =====================================================

_instance: Optional[AmadeusService] = None
_instance_lock = threading.Lock()


def get_amadeus_service() -> AmadeusService:
    """
    Return the singleton AmadeusService instance.
    Instantiated on first call (lazy init).
    Thread-safe.
    """
    global _instance
    if _instance is None:
        with _instance_lock:
            if _instance is None:
                _instance = AmadeusService()
    return _instance