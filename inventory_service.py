"""
inventory_service.py — Admin-Controlled Inventory Service
==========================================================
Version 2.0 — Enterprise OTA Platform

Responsibilities (STRICT):
  - Fetch hotels, cabs, sightseeing, addons, transports from PostgreSQL
  - Active/inactive filtering
  - Region + client scoping on ALL queries
  - Structured result normalization (internal schema only)
  - No pricing calculations (deferred to pricing_engine.py)
  - No Amadeus calls (deferred to amadeus_service.py)

Query patterns:
  - All methods accept db_connection (caller manages lifecycle)
  - Returns typed dicts or InventoryItem dataclasses
  - All queries are parameterized — no SQL injection vectors
  - Caller is responsible for cursor cleanup

Schema assumptions:
  - hotels, cabs, destinations, addons, transports, regions tables
  - pricing range tables: hotel_pricing_ranges, transport_pricing_ranges, addon_pricing_ranges
  - See expedia_schema.sql for full DDL

Extensibility:
  - Add new inventory types by subclassing InventoryFetcher
  - Swap DB backend by implementing InventoryBackend protocol
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional, Tuple
from decimal import Decimal

import psycopg2.extras

logger = logging.getLogger(__name__)


# =====================================================
# EXCEPTIONS
# =====================================================

class InventoryError(Exception):
    """Base inventory service error."""

class InventoryNotFoundError(InventoryError):
    """Requested entity not found."""

class InventoryQueryError(InventoryError):
    """DB query failure."""


# =====================================================
# DATA MODELS
# =====================================================

@dataclass
class HotelRecord:
    id: int
    client_id: int
    region_id: int
    name: str
    internal_name: str
    display_name: str
    hotel_type: str
    star_rating: int
    location: str
    address: str
    city: str
    description: str
    amenities: List[str]
    images: List[str]
    adult_rate_peak: Decimal
    child_rate_peak: Decimal
    adult_rate_off: Decimal
    child_rate_off: Decimal
    sharing_capacity: int
    active: bool
    pricing_ranges: List[Dict] = field(default_factory=list)

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['adult_rate_peak'] = float(self.adult_rate_peak)
        d['child_rate_peak'] = float(self.child_rate_peak)
        d['adult_rate_off']  = float(self.adult_rate_off)
        d['child_rate_off']  = float(self.child_rate_off)
        return d


@dataclass
class CabRecord:
    id: int
    client_id: int
    region_id: int
    name: str
    cab_type: str
    display_name: str
    capacity: int
    rate_per_km: Decimal
    rate_per_day: Decimal
    rate_flat: Decimal
    pricing_type: str
    active: bool

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['rate_per_km']  = float(self.rate_per_km)
        d['rate_per_day'] = float(self.rate_per_day)
        d['rate_flat']    = float(self.rate_flat)
        return d


@dataclass
class SightseeingRecord:
    id: int
    client_id: int
    region_id: int
    name: str
    internal_name: str
    display_name: str
    destination_type: str
    is_special: bool
    base_rate: Decimal
    per_day_rate: Decimal
    free_sightseeing_days: int
    active: bool
    pricing_ranges: List[Dict] = field(default_factory=list)

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['base_rate']    = float(self.base_rate)
        d['per_day_rate'] = float(self.per_day_rate)
        return d


@dataclass
class AddonRecord:
    id: int
    client_id: int
    region_id: int
    name: str
    internal_name: str
    display_name: str
    addon_type: str
    rate_peak: Decimal
    rate_off: Decimal
    pricing_basis: str
    active: bool
    pricing_ranges: List[Dict] = field(default_factory=list)

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['rate_peak'] = float(self.rate_peak)
        d['rate_off']  = float(self.rate_off)
        return d


@dataclass
class TransportRecord:
    id: int
    client_id: int
    region_id: int
    name: str
    transport_type: str
    display_name: str
    seat_capacity: int
    adult_rate_peak: Decimal
    child_rate_peak: Decimal
    adult_rate_off: Decimal
    child_rate_off: Decimal
    peak_pricing_type: str
    off_pricing_type: str
    trip_type: str
    return_rate_multiplier: Decimal
    active: bool
    pricing_ranges: List[Dict] = field(default_factory=list)

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['adult_rate_peak']        = float(self.adult_rate_peak)
        d['child_rate_peak']        = float(self.child_rate_peak)
        d['adult_rate_off']         = float(self.adult_rate_off)
        d['child_rate_off']         = float(self.child_rate_off)
        d['return_rate_multiplier'] = float(self.return_rate_multiplier)
        return d


@dataclass
class RegionRecord:
    id: int
    client_id: int
    name: str
    currency: str
    is_domestic: bool
    service_percent: Decimal
    booking_percent: Decimal
    active: bool

    def to_dict(self) -> Dict:
        d = asdict(self)
        d['service_percent'] = float(self.service_percent)
        d['booking_percent'] = float(self.booking_percent)
        return d


# =====================================================
# INVENTORY SERVICE
# =====================================================

class InventoryService:
    """
    Single-responsibility service for fetching admin-controlled inventory from DB.

    All methods accept an active psycopg2 connection.
    The caller (app.py route or merge_service.py) manages connection lifecycle.

    Example:
        svc = InventoryService()
        hotels = svc.get_hotels(conn, client_id=1, region_id=2, active_only=True)
    """

    # ── Regions ────────────────────────────────────────────────────────────────

    def get_region(
        self,
        conn,
        region_id: int,
        client_id: int = 1,
    ) -> Optional[RegionRecord]:
        """Fetch a single region by ID."""
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                SELECT id, client_id, name, currency, is_domestic,
                       service_percent, booking_percent, active
                FROM regions
                WHERE id = %s AND client_id = %s AND active = TRUE
                """,
                (region_id, client_id),
            )
            row = cur.fetchone()
        if not row:
            return None
        return self._map_region(row)

    def get_all_regions(self, conn, client_id: int = 1) -> List[RegionRecord]:
        """Fetch all active regions for a client."""
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                SELECT id, client_id, name, currency, is_domestic,
                       service_percent, booking_percent, active
                FROM regions
                WHERE client_id = %s AND active = TRUE
                ORDER BY name
                """,
                (client_id,),
            )
            rows = cur.fetchall()
        return [self._map_region(r) for r in rows]

    # ── Hotels ─────────────────────────────────────────────────────────────────

    def get_hotels(
        self,
        conn,
        client_id: int,
        region_id: Optional[int] = None,
        active_only: bool = True,
        with_pricing_ranges: bool = True,
    ) -> List[HotelRecord]:
        """
        Fetch hotels from DB.

        Args:
            conn:                 psycopg2 connection
            client_id:           Client scope
            region_id:           Optional region filter
            active_only:         If True, only return active hotels
            with_pricing_ranges: Attach pricing range records
        """
        conditions = ['h.client_id = %s']
        params: List[Any] = [client_id]

        if region_id is not None:
            conditions.append('h.region_id = %s')
            params.append(region_id)

        if active_only:
            conditions.append('h.active = TRUE')

        where = ' AND '.join(conditions)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT
                    h.id, h.client_id, h.region_id,
                    h.name, h.internal_name, h.display_name,
                    COALESCE(h.hotel_type, 'STANDARD') AS hotel_type,
                    COALESCE(h.star_rating, 3) AS star_rating,
                    COALESCE(h.location, '') AS location,
                    COALESCE(h.address, '') AS address,
                    COALESCE(h.city, '') AS city,
                    COALESCE(h.description, '') AS description,
                    COALESCE(h.amenities, ARRAY[]::text[]) AS amenities,
                    COALESCE(h.images, ARRAY[]::text[]) AS images,
                    h.adult_rate_peak, h.child_rate_peak,
                    h.adult_rate_off, h.child_rate_off,
                    COALESCE(h.sharing_capacity, 2) AS sharing_capacity,
                    h.active
                FROM hotels h
                WHERE {where}
                ORDER BY h.name
                """,
                params,
            )
            rows = cur.fetchall()

        hotels = [self._map_hotel(r) for r in rows]

        if with_pricing_ranges and hotels:
            hotel_ids = [h.id for h in hotels]
            ranges_by_hotel = self._fetch_hotel_pricing_ranges(conn, hotel_ids, client_id)
            for hotel in hotels:
                hotel.pricing_ranges = ranges_by_hotel.get(hotel.id, [])

        return hotels

    def get_hotel_by_internal_name(
        self,
        conn,
        internal_name: str,
        client_id: int,
        region_id: Optional[int] = None,
    ) -> Optional[HotelRecord]:
        """Fetch a single hotel by its internal_name key."""
        conditions = ['h.client_id = %s', 'h.internal_name = %s', 'h.active = TRUE']
        params: List[Any] = [client_id, internal_name]
        if region_id:
            conditions.append('h.region_id = %s')
            params.append(region_id)

        where = ' AND '.join(conditions)
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT h.id, h.client_id, h.region_id, h.name, h.internal_name,
                    h.display_name,
                    COALESCE(h.hotel_type, 'STANDARD') AS hotel_type,
                    COALESCE(h.star_rating, 3) AS star_rating,
                    COALESCE(h.location, '') AS location,
                    COALESCE(h.address, '') AS address,
                    COALESCE(h.city, '') AS city,
                    COALESCE(h.description, '') AS description,
                    COALESCE(h.amenities, ARRAY[]::text[]) AS amenities,
                    COALESCE(h.images, ARRAY[]::text[]) AS images,
                    h.adult_rate_peak, h.child_rate_peak,
                    h.adult_rate_off, h.child_rate_off,
                    COALESCE(h.sharing_capacity, 2) AS sharing_capacity,
                    h.active
                FROM hotels h WHERE {where}
                """,
                params,
            )
            row = cur.fetchone()

        if not row:
            return None

        hotel = self._map_hotel(row)
        ranges = self._fetch_hotel_pricing_ranges(conn, [hotel.id], client_id)
        hotel.pricing_ranges = ranges.get(hotel.id, [])
        return hotel

    # ── Cabs ───────────────────────────────────────────────────────────────────

    def get_cabs(
        self,
        conn,
        client_id: int,
        region_id: Optional[int] = None,
        active_only: bool = True,
    ) -> List[CabRecord]:
        """Fetch cab inventory for a client/region."""
        conditions = ['client_id = %s']
        params: List[Any] = [client_id]

        if region_id is not None:
            conditions.append('region_id = %s')
            params.append(region_id)
        if active_only:
            conditions.append('active = TRUE')

        where = ' AND '.join(conditions)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT id, client_id, region_id, name,
                    COALESCE(cab_type, 'SEDAN') AS cab_type,
                    display_name,
                    COALESCE(capacity, 4) AS capacity,
                    COALESCE(rate_per_km, 0) AS rate_per_km,
                    COALESCE(rate_per_day, 0) AS rate_per_day,
                    COALESCE(rate_flat, 0) AS rate_flat,
                    COALESCE(pricing_type, 'per_vehicle') AS pricing_type,
                    active
                FROM cabs
                WHERE {where}
                ORDER BY name
                """,
                params,
            )
            rows = cur.fetchall()

        return [self._map_cab(r) for r in rows]

    # ── Sightseeing (destinations) ─────────────────────────────────────────────

    def get_sightseeing(
        self,
        conn,
        client_id: int,
        region_id: Optional[int] = None,
        active_only: bool = True,
        with_pricing_ranges: bool = True,
    ) -> List[SightseeingRecord]:
        """Fetch sightseeing / destination records."""
        conditions = ['d.client_id = %s']
        params: List[Any] = [client_id]

        if region_id is not None:
            conditions.append('d.region_id = %s')
            params.append(region_id)
        if active_only:
            conditions.append('d.active = TRUE')

        where = ' AND '.join(conditions)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT d.id, d.client_id, d.region_id,
                    d.name, d.internal_name, d.display_name,
                    COALESCE(d.destination_type, 'CITY') AS destination_type,
                    d.is_special,
                    d.base_rate, d.per_day_rate,
                    COALESCE(d.free_sightseeing_days, 0) AS free_sightseeing_days,
                    d.active
                FROM destinations d
                WHERE {where}
                ORDER BY d.name
                """,
                params,
            )
            rows = cur.fetchall()

        records = [self._map_sightseeing(r) for r in rows]

        if with_pricing_ranges and records:
            # Sightseeing pricing ranges (reuse destination_pricing_ranges if present)
            # Falls back to base_rate if no ranges configured
            pass  # Future: attach pricing_ranges when table exists

        return records

    # ── Addons ─────────────────────────────────────────────────────────────────

    def get_addons(
        self,
        conn,
        client_id: int,
        region_id: Optional[int] = None,
        active_only: bool = True,
        with_pricing_ranges: bool = True,
    ) -> List[AddonRecord]:
        """Fetch addon inventory."""
        conditions = ['a.client_id = %s']
        params: List[Any] = [client_id]

        if region_id is not None:
            conditions.append('a.region_id = %s')
            params.append(region_id)
        if active_only:
            conditions.append('a.active = TRUE')

        where = ' AND '.join(conditions)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT a.id, a.client_id, a.region_id,
                    a.name, a.internal_name, a.display_name,
                    COALESCE(a.addon_type, 'GENERAL') AS addon_type,
                    a.rate_peak, a.rate_off,
                    COALESCE(a.pricing_basis, 'per_person') AS pricing_basis,
                    a.active
                FROM addons a
                WHERE {where}
                ORDER BY a.name
                """,
                params,
            )
            rows = cur.fetchall()

        addons = [self._map_addon(r) for r in rows]

        if with_pricing_ranges and addons:
            addon_ids = [a.id for a in addons]
            ranges_by_addon = self._fetch_addon_pricing_ranges(conn, addon_ids, client_id)
            for addon in addons:
                addon.pricing_ranges = ranges_by_addon.get(addon.id, [])

        return addons

    # ── Transports ─────────────────────────────────────────────────────────────

    def get_transports(
        self,
        conn,
        client_id: int,
        region_id: Optional[int] = None,
        active_only: bool = True,
        with_pricing_ranges: bool = True,
    ) -> List[TransportRecord]:
        """Fetch transport inventory."""
        conditions = ['t.client_id = %s']
        params: List[Any] = [client_id]

        if region_id is not None:
            conditions.append('t.region_id = %s')
            params.append(region_id)
        if active_only:
            conditions.append('t.active = TRUE')

        where = ' AND '.join(conditions)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT t.id, t.client_id, t.region_id,
                    t.name, t.transport_type, t.display_name,
                    t.seat_capacity, t.adult_rate_peak, t.child_rate_peak,
                    t.adult_rate_off, t.child_rate_off,
                    t.peak_pricing_type, t.off_pricing_type,
                    t.trip_type, t.return_rate_multiplier,
                    t.active
                FROM transports t
                WHERE {where}
                ORDER BY t.name
                """,
                params,
            )
            rows = cur.fetchall()

        transports = [self._map_transport(r) for r in rows]

        if with_pricing_ranges and transports:
            transport_ids = [t.id for t in transports]
            ranges_by_transport = self._fetch_transport_pricing_ranges(
                conn, transport_ids, client_id
            )
            for transport in transports:
                transport.pricing_ranges = ranges_by_transport.get(transport.id, [])

        return transports

    # ── Bundle availability ────────────────────────────────────────────────────

    def get_bundle_availability(
        self,
        conn,
        client_id: int,
        region_id: int,
    ) -> Dict[str, Any]:
        """
        Return a complete inventory snapshot for bundle construction.
        Used by merge_service.py to build package options.
        """
        return {
            'hotels':      [h.to_dict() for h in self.get_hotels(conn, client_id, region_id)],
            'cabs':        [c.to_dict() for c in self.get_cabs(conn, client_id, region_id)],
            'sightseeing': [s.to_dict() for s in self.get_sightseeing(conn, client_id, region_id)],
            'addons':      [a.to_dict() for a in self.get_addons(conn, client_id, region_id)],
            'transports':  [t.to_dict() for t in self.get_transports(conn, client_id, region_id)],
        }

    # ── Pricing range helpers ──────────────────────────────────────────────────

    def _fetch_hotel_pricing_ranges(
        self,
        conn,
        hotel_ids: List[int],
        client_id: int,
    ) -> Dict[int, List[Dict]]:
        if not hotel_ids:
            return {}
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                SELECT hotel_id, id, label, start_date, end_date,
                       adult_rate, child_rate, active
                FROM hotel_pricing_ranges
                WHERE hotel_id = ANY(%s) AND client_id = %s AND active = TRUE
                ORDER BY start_date
                """,
                (hotel_ids, client_id),
            )
            rows = cur.fetchall()

        result: Dict[int, List[Dict]] = {}
        for row in rows:
            hid = row['hotel_id']
            result.setdefault(hid, []).append({
                'id': row['id'],
                'label': row['label'],
                'start_date': str(row['start_date']),
                'end_date': str(row['end_date']),
                'adult_rate': float(row['adult_rate']),
                'child_rate': float(row['child_rate']),
            })
        return result

    def _fetch_addon_pricing_ranges(
        self,
        conn,
        addon_ids: List[int],
        client_id: int,
    ) -> Dict[int, List[Dict]]:
        if not addon_ids:
            return {}
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                SELECT addon_id, id, label, start_date, end_date, rate, active
                FROM addon_pricing_ranges
                WHERE addon_id = ANY(%s) AND client_id = %s AND active = TRUE
                ORDER BY start_date
                """,
                (addon_ids, client_id),
            )
            rows = cur.fetchall()

        result: Dict[int, List[Dict]] = {}
        for row in rows:
            aid = row['addon_id']
            result.setdefault(aid, []).append({
                'id': row['id'],
                'label': row['label'],
                'start_date': str(row['start_date']),
                'end_date': str(row['end_date']),
                'rate': float(row['rate']),
            })
        return result

    def _fetch_transport_pricing_ranges(
        self,
        conn,
        transport_ids: List[int],
        client_id: int,
    ) -> Dict[int, List[Dict]]:
        if not transport_ids:
            return {}
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                SELECT transport_id, id, label, start_date, end_date,
                       adult_rate, child_rate, pricing_type, active
                FROM transport_pricing_ranges
                WHERE transport_id = ANY(%s) AND client_id = %s AND active = TRUE
                ORDER BY start_date
                """,
                (transport_ids, client_id),
            )
            rows = cur.fetchall()

        result: Dict[int, List[Dict]] = {}
        for row in rows:
            tid = row['transport_id']
            result.setdefault(tid, []).append({
                'id': row['id'],
                'label': row['label'],
                'start_date': str(row['start_date']),
                'end_date': str(row['end_date']),
                'adult_rate': float(row['adult_rate']),
                'child_rate': float(row['child_rate']),
                'pricing_type': row['pricing_type'],
            })
        return result

    # ── Mappers ────────────────────────────────────────────────────────────────

    @staticmethod
    def _map_region(row) -> RegionRecord:
        return RegionRecord(
            id=row['id'],
            client_id=row['client_id'],
            name=row['name'],
            currency=row['currency'],
            is_domestic=row['is_domestic'],
            service_percent=Decimal(str(row['service_percent'])),
            booking_percent=Decimal(str(row['booking_percent'])),
            active=row['active'],
        )

    @staticmethod
    def _map_hotel(row) -> HotelRecord:
        amenities = row.get('amenities') or []
        images    = row.get('images') or []
        # psycopg2 returns arrays as Python lists already
        if isinstance(amenities, str):
            amenities = [a.strip() for a in amenities.split(',') if a.strip()]
        if isinstance(images, str):
            images = [i.strip() for i in images.split(',') if i.strip()]

        return HotelRecord(
            id=row['id'],
            client_id=row['client_id'],
            region_id=row['region_id'],
            name=row['name'],
            internal_name=row['internal_name'],
            display_name=row['display_name'],
            hotel_type=row['hotel_type'],
            star_rating=int(row['star_rating'] or 3),
            location=row['location'],
            address=row['address'],
            city=row['city'],
            description=row['description'],
            amenities=list(amenities),
            images=list(images),
            adult_rate_peak=Decimal(str(row['adult_rate_peak'])),
            child_rate_peak=Decimal(str(row['child_rate_peak'])),
            adult_rate_off=Decimal(str(row['adult_rate_off'])),
            child_rate_off=Decimal(str(row['child_rate_off'])),
            sharing_capacity=int(row['sharing_capacity']),
            active=row['active'],
        )

    @staticmethod
    def _map_cab(row) -> CabRecord:
        return CabRecord(
            id=row['id'],
            client_id=row['client_id'],
            region_id=row['region_id'],
            name=row['name'],
            cab_type=row['cab_type'],
            display_name=row['display_name'],
            capacity=int(row['capacity']),
            rate_per_km=Decimal(str(row['rate_per_km'])),
            rate_per_day=Decimal(str(row['rate_per_day'])),
            rate_flat=Decimal(str(row['rate_flat'])),
            pricing_type=row['pricing_type'],
            active=row['active'],
        )

    @staticmethod
    def _map_sightseeing(row) -> SightseeingRecord:
        return SightseeingRecord(
            id=row['id'],
            client_id=row['client_id'],
            region_id=row['region_id'],
            name=row['name'],
            internal_name=row['internal_name'],
            display_name=row['display_name'],
            destination_type=row['destination_type'],
            is_special=bool(row['is_special']),
            base_rate=Decimal(str(row['base_rate'])),
            per_day_rate=Decimal(str(row['per_day_rate'])),
            free_sightseeing_days=int(row['free_sightseeing_days']),
            active=row['active'],
        )

    @staticmethod
    def _map_addon(row) -> AddonRecord:
        return AddonRecord(
            id=row['id'],
            client_id=row['client_id'],
            region_id=row['region_id'],
            name=row['name'],
            internal_name=row['internal_name'],
            display_name=row['display_name'],
            addon_type=row['addon_type'],
            rate_peak=Decimal(str(row['rate_peak'])),
            rate_off=Decimal(str(row['rate_off'])),
            pricing_basis=row['pricing_basis'],
            active=row['active'],
        )

    @staticmethod
    def _map_transport(row) -> TransportRecord:
        return TransportRecord(
            id=row['id'],
            client_id=row['client_id'],
            region_id=row['region_id'],
            name=row['name'],
            transport_type=row['transport_type'],
            display_name=row['display_name'],
            seat_capacity=int(row['seat_capacity']),
            adult_rate_peak=Decimal(str(row['adult_rate_peak'])),
            child_rate_peak=Decimal(str(row['child_rate_peak'])),
            adult_rate_off=Decimal(str(row['adult_rate_off'])),
            child_rate_off=Decimal(str(row['child_rate_off'])),
            peak_pricing_type=row['peak_pricing_type'],
            off_pricing_type=row['off_pricing_type'],
            trip_type=row['trip_type'],
            return_rate_multiplier=Decimal(str(row['return_rate_multiplier'])),
            active=row['active'],
        )


# =====================================================
# SINGLETON
# =====================================================

_inventory_service: Optional[InventoryService] = None


def get_inventory_service() -> InventoryService:
    """Return singleton InventoryService instance."""
    global _inventory_service
    if _inventory_service is None:
        _inventory_service = InventoryService()
    return _inventory_service