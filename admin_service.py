"""
admin_service.py — Admin Operations Service
============================================
Version 2.0 — Enterprise OTA Platform

Responsibilities (STRICT):
  - CRUD for hotels, cabs, sightseeing, addons, transports, pricing rules
  - Pricing range management (date-range based pricing)
  - Bundle rule CRUD
  - Season / blackout date management
  - Active/inactive toggling with audit trail
  - Input validation before DB writes
  - No pricing calculations (deferred to pricing_engine.py)
  - No routing logic (deferred to app.py)

Security:
  - All writes require authenticated admin session (enforced in app.py decorator)
  - All queries are parameterized
  - Soft + hard delete support
  - Audit log entries on all mutations (writes to admin_audit_log table)

Audit log:
  - Table: admin_audit_log (created below if missing)
  - Fields: id, admin_user_id, entity_type, entity_id, action, before_json, after_json, created_at
  - All CREATE / UPDATE / DELETE / TOGGLE operations are logged
"""

from __future__ import annotations

import json
import logging
from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation
from typing import Any, Dict, List, Optional, Tuple

import psycopg2
import psycopg2.extras

logger = logging.getLogger(__name__)


# =====================================================
# EXCEPTIONS
# =====================================================

class AdminServiceError(Exception):
    """Base admin service error."""

class AdminValidationError(AdminServiceError):
    """Input validation failure."""

class AdminNotFoundError(AdminServiceError):
    """Entity not found in DB."""

class AdminConflictError(AdminServiceError):
    """Unique constraint violation."""


# =====================================================
# VALIDATION HELPERS
# =====================================================

def _require(value: Any, field_name: str) -> Any:
    if value is None or (isinstance(value, str) and not value.strip()):
        raise AdminValidationError(f"Field '{field_name}' is required.")
    return value


def _require_positive_decimal(value: Any, field_name: str) -> Decimal:
    try:
        d = Decimal(str(value))
        if d < 0:
            raise AdminValidationError(f"Field '{field_name}' must be >= 0.")
        return d
    except InvalidOperation:
        raise AdminValidationError(f"Field '{field_name}' must be a valid number.")


def _require_int(value: Any, field_name: str, min_val: int = 0) -> int:
    try:
        i = int(value)
        if i < min_val:
            raise AdminValidationError(f"Field '{field_name}' must be >= {min_val}.")
        return i
    except (ValueError, TypeError):
        raise AdminValidationError(f"Field '{field_name}' must be a valid integer.")


def _slug_from_name(name: str) -> str:
    """Generate a URL-safe slug from a display name."""
    import re
    slug = name.lower().strip()
    slug = re.sub(r'[^\w\s-]', '', slug)
    slug = re.sub(r'[\s_]+', '-', slug)
    slug = re.sub(r'-+', '-', slug).strip('-')
    return slug[:80]


# =====================================================
# AUDIT LOG
# =====================================================

def _write_audit(
    conn,
    admin_user_id: Optional[int],
    entity_type: str,
    entity_id: Optional[int],
    action: str,
    before: Optional[Dict] = None,
    after: Optional[Dict] = None,
) -> None:
    """Write an audit log entry. Fails silently to not block operations."""
    try:
        with conn.cursor() as cur:
            cur.execute(
                """
                INSERT INTO admin_audit_log
                    (admin_user_id, entity_type, entity_id, action, before_json, after_json, created_at)
                VALUES (%s, %s, %s, %s, %s, %s, NOW())
                ON CONFLICT DO NOTHING
                """,
                (
                    admin_user_id,
                    entity_type,
                    entity_id,
                    action,
                    json.dumps(before, default=str) if before else None,
                    json.dumps(after, default=str) if after else None,
                ),
            )
    except Exception as e:
        logger.warning(f"Audit log write failed (non-critical): {e}")


# =====================================================
# ADMIN SERVICE
# =====================================================

class AdminService:
    """
    Admin CRUD operations service.

    All methods accept:
      - conn:         Active psycopg2 connection
      - admin_user_id: Authenticated admin ID (for audit log)
      - data:         Input dict from request (validated internally)
    """

    # ── Hotels ─────────────────────────────────────────────────────────────────

    def create_hotel(
        self,
        conn,
        admin_user_id: int,
        data: Dict,
        client_id: int = 1,
    ) -> Dict:
        """
        Create a new hotel.

        Required fields: name, region_id, display_name
        Optional: hotel_type, star_rating, location, city, description,
                  adult_rate_peak, child_rate_peak, adult_rate_off, child_rate_off,
                  sharing_capacity, active
        """
        name         = _require(data.get('name'), 'name')
        region_id    = _require_int(data.get('region_id'), 'region_id', min_val=1)
        display_name = data.get('display_name') or name
        internal_name = data.get('internal_name') or _slug_from_name(name)

        hotel_type      = data.get('hotel_type', 'STANDARD')
        star_rating     = _require_int(data.get('star_rating', 3), 'star_rating')
        location        = data.get('location', '')
        city            = data.get('city', '')
        address         = data.get('address', '')
        description     = data.get('description', '')
        sharing_capacity = _require_int(data.get('sharing_capacity', 2), 'sharing_capacity', min_val=1)

        adult_rate_peak = _require_positive_decimal(data.get('adult_rate_peak', 0), 'adult_rate_peak')
        child_rate_peak = _require_positive_decimal(data.get('child_rate_peak', 0), 'child_rate_peak')
        adult_rate_off  = _require_positive_decimal(data.get('adult_rate_off', 0), 'adult_rate_off')
        child_rate_off  = _require_positive_decimal(data.get('child_rate_off', 0), 'child_rate_off')
        active          = bool(data.get('active', True))

        amenities = json.dumps(data.get('amenities', [])) if isinstance(data.get('amenities'), list) else '[]'
        images    = json.dumps(data.get('images', []))    if isinstance(data.get('images'), list)    else '[]'

        try:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    INSERT INTO hotels
                        (client_id, region_id, name, internal_name, display_name,
                         hotel_type, star_rating, location, city, address, description,
                         adult_rate_peak, child_rate_peak, adult_rate_off, child_rate_off,
                         sharing_capacity, active, created_at, updated_at)
                    VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                    RETURNING *
                    """,
                    (
                        client_id, region_id, name, internal_name, display_name,
                        hotel_type, star_rating, location, city, address, description,
                        adult_rate_peak, child_rate_peak, adult_rate_off, child_rate_off,
                        sharing_capacity, active,
                    ),
                )
                row = cur.fetchone()
                conn.commit()
        except psycopg2.IntegrityError as e:
            conn.rollback()
            raise AdminConflictError(
                f"Hotel '{internal_name}' already exists in this region."
            )

        _write_audit(conn, admin_user_id, 'hotel', row['id'], 'CREATE', after=dict(row))
        return dict(row)

    def update_hotel(
        self,
        conn,
        admin_user_id: int,
        hotel_id: int,
        data: Dict,
        client_id: int = 1,
    ) -> Dict:
        """Update an existing hotel. Partial updates supported."""
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                'SELECT * FROM hotels WHERE id = %s AND client_id = %s',
                (hotel_id, client_id)
            )
            existing = cur.fetchone()

        if not existing:
            raise AdminNotFoundError(f"Hotel {hotel_id} not found.")

        before = dict(existing)

        # Merge fields
        updated = {**before}
        for field_name in (
            'name', 'display_name', 'hotel_type', 'location', 'city',
            'address', 'description', 'active',
        ):
            if field_name in data:
                updated[field_name] = data[field_name]

        for rate_field in ('adult_rate_peak', 'child_rate_peak', 'adult_rate_off', 'child_rate_off'):
            if rate_field in data:
                updated[rate_field] = _require_positive_decimal(data[rate_field], rate_field)

        if 'star_rating' in data:
            updated['star_rating'] = _require_int(data['star_rating'], 'star_rating')
        if 'sharing_capacity' in data:
            updated['sharing_capacity'] = _require_int(data['sharing_capacity'], 'sharing_capacity', 1)

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                UPDATE hotels SET
                    name=%s, display_name=%s, hotel_type=%s, star_rating=%s,
                    location=%s, city=%s, address=%s, description=%s,
                    adult_rate_peak=%s, child_rate_peak=%s,
                    adult_rate_off=%s, child_rate_off=%s,
                    sharing_capacity=%s, active=%s, updated_at=NOW()
                WHERE id=%s AND client_id=%s
                RETURNING *
                """,
                (
                    updated['name'], updated['display_name'], updated['hotel_type'],
                    updated['star_rating'], updated['location'], updated['city'],
                    updated['address'], updated['description'],
                    updated['adult_rate_peak'], updated['child_rate_peak'],
                    updated['adult_rate_off'], updated['child_rate_off'],
                    updated['sharing_capacity'], updated['active'],
                    hotel_id, client_id,
                ),
            )
            row = cur.fetchone()
            conn.commit()

        _write_audit(conn, admin_user_id, 'hotel', hotel_id, 'UPDATE', before=before, after=dict(row))
        return dict(row)

    def delete_hotel(
        self,
        conn,
        admin_user_id: int,
        hotel_id: int,
        client_id: int = 1,
        hard_delete: bool = True,
    ) -> bool:
        """Hard or soft delete a hotel."""
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute('SELECT * FROM hotels WHERE id=%s AND client_id=%s', (hotel_id, client_id))
            existing = cur.fetchone()

        if not existing:
            raise AdminNotFoundError(f"Hotel {hotel_id} not found.")

        before = dict(existing)

        if hard_delete:
            with conn.cursor() as cur:
                cur.execute('DELETE FROM hotels WHERE id=%s AND client_id=%s', (hotel_id, client_id))
                conn.commit()
            _write_audit(conn, admin_user_id, 'hotel', hotel_id, 'HARD_DELETE', before=before)
        else:
            with conn.cursor() as cur:
                cur.execute(
                    'UPDATE hotels SET active=FALSE, updated_at=NOW() WHERE id=%s AND client_id=%s',
                    (hotel_id, client_id)
                )
                conn.commit()
            _write_audit(conn, admin_user_id, 'hotel', hotel_id, 'SOFT_DELETE', before=before)

        return True

    def toggle_hotel(
        self,
        conn,
        admin_user_id: int,
        hotel_id: int,
        client_id: int = 1,
    ) -> Dict:
        """Toggle hotel active/inactive. Returns new state."""
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                UPDATE hotels SET active = NOT active, updated_at = NOW()
                WHERE id=%s AND client_id=%s RETURNING id, active
                """,
                (hotel_id, client_id)
            )
            row = cur.fetchone()
            conn.commit()

        if not row:
            raise AdminNotFoundError(f"Hotel {hotel_id} not found.")

        _write_audit(conn, admin_user_id, 'hotel', hotel_id, 'TOGGLE', after=dict(row))
        return {'id': row['id'], 'active': row['active']}

    # ── Pricing ranges ─────────────────────────────────────────────────────────

    def upsert_hotel_pricing_range(
        self,
        conn,
        admin_user_id: int,
        hotel_id: int,
        data: Dict,
        client_id: int = 1,
    ) -> Dict:
        """
        Create or update a hotel pricing range.
        If data contains 'id', it's an update. Otherwise creates new.
        """
        label      = data.get('label', 'Custom Range')
        start_date = _require(data.get('start_date'), 'start_date')
        end_date   = _require(data.get('end_date'), 'end_date')
        adult_rate = _require_positive_decimal(data.get('adult_rate', 0), 'adult_rate')
        child_rate = _require_positive_decimal(data.get('child_rate', 0), 'child_rate')
        range_id   = data.get('id')

        if range_id:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    UPDATE hotel_pricing_ranges
                    SET label=%s, start_date=%s, end_date=%s,
                        adult_rate=%s, child_rate=%s, updated_at=NOW()
                    WHERE id=%s AND hotel_id=%s AND client_id=%s
                    RETURNING *
                    """,
                    (label, start_date, end_date, adult_rate, child_rate,
                     range_id, hotel_id, client_id),
                )
                row = cur.fetchone()
                conn.commit()
        else:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    INSERT INTO hotel_pricing_ranges
                        (client_id, hotel_id, label, start_date, end_date, adult_rate, child_rate)
                    VALUES (%s,%s,%s,%s,%s,%s,%s)
                    RETURNING *
                    """,
                    (client_id, hotel_id, label, start_date, end_date, adult_rate, child_rate),
                )
                row = cur.fetchone()
                conn.commit()

        if not row:
            raise AdminNotFoundError("Pricing range not found after upsert.")

        _write_audit(conn, admin_user_id, 'hotel_pricing_range', row['id'],
                     'UPDATE' if range_id else 'CREATE', after=dict(row))
        return dict(row)

    def delete_pricing_range(
        self,
        conn,
        admin_user_id: int,
        range_id: int,
        entity_type: str,  # 'hotel' | 'transport' | 'addon'
        client_id: int = 1,
    ) -> bool:
        """Delete a pricing range by ID."""
        table_map = {
            'hotel':     'hotel_pricing_ranges',
            'transport': 'transport_pricing_ranges',
            'addon':     'addon_pricing_ranges',
        }
        table = table_map.get(entity_type)
        if not table:
            raise AdminValidationError(f"Unknown entity_type: {entity_type}")

        with conn.cursor() as cur:
            cur.execute(
                f'DELETE FROM {table} WHERE id=%s AND client_id=%s',
                (range_id, client_id)
            )
            conn.commit()

        _write_audit(conn, admin_user_id, f'{entity_type}_pricing_range', range_id, 'DELETE')
        return True

    # ── Cabs ───────────────────────────────────────────────────────────────────

    def create_cab(self, conn, admin_user_id: int, data: Dict, client_id: int = 1) -> Dict:
        """Create a new cab."""
        name        = _require(data.get('name'), 'name')
        region_id   = _require_int(data.get('region_id'), 'region_id', min_val=1)
        display_name = data.get('display_name') or name
        cab_type    = data.get('cab_type', 'SEDAN')
        capacity    = _require_int(data.get('capacity', 4), 'capacity', min_val=1)
        rate_per_km  = _require_positive_decimal(data.get('rate_per_km', 0), 'rate_per_km')
        rate_per_day = _require_positive_decimal(data.get('rate_per_day', 0), 'rate_per_day')
        rate_flat    = _require_positive_decimal(data.get('rate_flat', 0), 'rate_flat')
        pricing_type = data.get('pricing_type', 'per_vehicle')
        active       = bool(data.get('active', True))

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                INSERT INTO cabs
                    (client_id, region_id, name, display_name, cab_type, capacity,
                     rate_per_km, rate_per_day, rate_flat, pricing_type, active,
                     created_at, updated_at)
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                RETURNING *
                """,
                (client_id, region_id, name, display_name, cab_type, capacity,
                 rate_per_km, rate_per_day, rate_flat, pricing_type, active),
            )
            row = cur.fetchone()
            conn.commit()

        _write_audit(conn, admin_user_id, 'cab', row['id'], 'CREATE', after=dict(row))
        return dict(row)

    def toggle_entity(
        self,
        conn,
        admin_user_id: int,
        entity_type: str,
        entity_id: int,
        client_id: int = 1,
    ) -> Dict:
        """
        Generic toggle active/inactive for any entity.
        entity_type: 'hotel' | 'cab' | 'addon' | 'transport' | 'destination'
        """
        table_map = {
            'hotel':       'hotels',
            'cab':         'cabs',
            'addon':       'addons',
            'transport':   'transports',
            'destination': 'destinations',
        }
        table = table_map.get(entity_type)
        if not table:
            raise AdminValidationError(f"Unknown entity_type: {entity_type}")

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                UPDATE {table} SET active = NOT active, updated_at = NOW()
                WHERE id = %s AND client_id = %s
                RETURNING id, active
                """,
                (entity_id, client_id),
            )
            row = cur.fetchone()
            conn.commit()

        if not row:
            raise AdminNotFoundError(f"{entity_type} {entity_id} not found.")

        _write_audit(conn, admin_user_id, entity_type, entity_id, 'TOGGLE', after=dict(row))
        return {'id': row['id'], 'active': row['active'], 'entity_type': entity_type}

    # ── Sightseeing ────────────────────────────────────────────────────────────

    def create_sightseeing(self, conn, admin_user_id: int, data: Dict, client_id: int = 1) -> Dict:
        """Create a sightseeing / destination record."""
        name         = _require(data.get('name'), 'name')
        region_id    = _require_int(data.get('region_id'), 'region_id', min_val=1)
        display_name = data.get('display_name') or name
        internal_name = data.get('internal_name') or _slug_from_name(name)
        dest_type    = data.get('destination_type', 'CITY')
        is_special   = int(bool(data.get('is_special', False)))
        base_rate    = _require_positive_decimal(data.get('base_rate', 0), 'base_rate')
        per_day_rate = _require_positive_decimal(data.get('per_day_rate', 0), 'per_day_rate')
        free_days    = _require_int(data.get('free_sightseeing_days', 0), 'free_sightseeing_days')
        active       = bool(data.get('active', True))

        try:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    INSERT INTO destinations
                        (client_id, region_id, name, internal_name, display_name,
                         destination_type, is_special, base_rate, per_day_rate,
                         free_sightseeing_days, active, created_at, updated_at)
                    VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                    RETURNING *
                    """,
                    (client_id, region_id, name, internal_name, display_name,
                     dest_type, is_special, base_rate, per_day_rate, free_days, active),
                )
                row = cur.fetchone()
                conn.commit()
        except psycopg2.IntegrityError:
            conn.rollback()
            raise AdminConflictError(f"Sightseeing '{internal_name}' already exists.")

        _write_audit(conn, admin_user_id, 'destination', row['id'], 'CREATE', after=dict(row))
        return dict(row)

    # ── Addons ─────────────────────────────────────────────────────────────────

    def create_addon(self, conn, admin_user_id: int, data: Dict, client_id: int = 1) -> Dict:
        """Create a new addon."""
        name          = _require(data.get('name'), 'name')
        region_id     = _require_int(data.get('region_id'), 'region_id', min_val=1)
        display_name  = data.get('display_name') or name
        internal_name = data.get('internal_name') or _slug_from_name(name)
        addon_type    = data.get('addon_type', 'GENERAL')
        rate_peak     = _require_positive_decimal(data.get('rate_peak', 0), 'rate_peak')
        rate_off      = _require_positive_decimal(data.get('rate_off', 0), 'rate_off')
        pricing_basis = data.get('pricing_basis', 'per_person')
        active        = bool(data.get('active', True))

        try:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    INSERT INTO addons
                        (client_id, region_id, name, internal_name, display_name,
                         addon_type, rate_peak, rate_off, pricing_basis, active,
                         created_at, updated_at)
                    VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                    RETURNING *
                    """,
                    (client_id, region_id, name, internal_name, display_name,
                     addon_type, rate_peak, rate_off, pricing_basis, active),
                )
                row = cur.fetchone()
                conn.commit()
        except psycopg2.IntegrityError:
            conn.rollback()
            raise AdminConflictError(f"Addon '{internal_name}' already exists.")

        _write_audit(conn, admin_user_id, 'addon', row['id'], 'CREATE', after=dict(row))
        return dict(row)

    # ── Pricing rules ──────────────────────────────────────────────────────────

    def create_pricing_rule(self, conn, admin_user_id: int, data: Dict, client_id: int = 1) -> Dict:
        """
        Create a dynamic pricing rule.

        Required: rule_name, entity_type, condition_json, action_json
        Optional: entity_id, priority, active, valid_from, valid_to
        """
        rule_name    = _require(data.get('rule_name'), 'rule_name')
        entity_type  = _require(data.get('entity_type'), 'entity_type')
        condition_j  = data.get('condition_json', '{}')
        action_j     = data.get('action_json', '{}')
        entity_id    = data.get('entity_id')
        priority     = _require_int(data.get('priority', 100), 'priority')
        active       = bool(data.get('active', True))
        valid_from   = data.get('valid_from')
        valid_to     = data.get('valid_to')

        # Validate JSON
        for j_field, j_val in [('condition_json', condition_j), ('action_json', action_j)]:
            if isinstance(j_val, dict):
                j_val = json.dumps(j_val)
            try:
                json.loads(j_val)
            except (json.JSONDecodeError, TypeError):
                raise AdminValidationError(f"Field '{j_field}' must be valid JSON.")

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                """
                INSERT INTO pricing_rules
                    (client_id, entity_type, entity_id, rule_name, condition_json,
                     action_json, priority, active, valid_from, valid_to,
                     created_at, updated_at)
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW(),NOW())
                RETURNING *
                """,
                (
                    client_id, entity_type, entity_id, rule_name,
                    condition_j if isinstance(condition_j, str) else json.dumps(condition_j),
                    action_j    if isinstance(action_j, str)    else json.dumps(action_j),
                    priority, active, valid_from, valid_to,
                ),
            )
            row = cur.fetchone()
            conn.commit()

        _write_audit(conn, admin_user_id, 'pricing_rule', row['id'], 'CREATE', after=dict(row))
        return dict(row)

    def list_pricing_rules(
        self,
        conn,
        client_id: int = 1,
        entity_type: Optional[str] = None,
        active_only: bool = False,
    ) -> List[Dict]:
        """List pricing rules with optional filters."""
        conditions = ['client_id = %s']
        params: List[Any] = [client_id]

        if entity_type:
            conditions.append('entity_type = %s')
            params.append(entity_type)
        if active_only:
            conditions.append('active = TRUE')

        where = ' AND '.join(conditions)
        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f'SELECT * FROM pricing_rules WHERE {where} ORDER BY priority, id',
                params,
            )
            rows = cur.fetchall()

        return [dict(r) for r in rows]

    # ── Bundle rules ───────────────────────────────────────────────────────────

    def upsert_bundle_rule(
        self,
        conn,
        admin_user_id: int,
        data: Dict,
        client_id: int = 1,
    ) -> Dict:
        """
        Create or update a bundle rule.
        Bundle rules define which hotel+cab+sightseeing combos are valid.
        Table: bundle_rules (created by schema migration below).
        """
        region_id    = _require_int(data.get('region_id'), 'region_id', min_val=1)
        rule_name    = _require(data.get('rule_name'), 'rule_name')
        hotel_ids    = data.get('hotel_ids', [])
        cab_ids      = data.get('cab_ids', [])
        addon_ids    = data.get('addon_ids', [])
        sight_ids    = data.get('sightseeing_ids', [])
        discount_pct = _require_positive_decimal(data.get('discount_percent', 0), 'discount_percent')
        active       = bool(data.get('active', True))
        rule_id      = data.get('id')

        rule_config = json.dumps({
            'hotel_ids': hotel_ids,
            'cab_ids': cab_ids,
            'addon_ids': addon_ids,
            'sightseeing_ids': sight_ids,
        })

        if rule_id:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    UPDATE bundle_rules SET
                        rule_name=%s, rule_config=%s, discount_percent=%s,
                        active=%s, updated_at=NOW()
                    WHERE id=%s AND client_id=%s
                    RETURNING *
                    """,
                    (rule_name, rule_config, discount_pct, active, rule_id, client_id),
                )
                row = cur.fetchone()
                conn.commit()
        else:
            with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                cur.execute(
                    """
                    INSERT INTO bundle_rules
                        (client_id, region_id, rule_name, rule_config, discount_percent,
                         active, created_at, updated_at)
                    VALUES (%s,%s,%s,%s,%s,%s,NOW(),NOW())
                    RETURNING *
                    """,
                    (client_id, region_id, rule_name, rule_config, discount_pct, active),
                )
                row = cur.fetchone()
                conn.commit()

        if not row:
            raise AdminNotFoundError("Bundle rule not found after upsert.")

        _write_audit(conn, admin_user_id, 'bundle_rule', row['id'],
                     'UPDATE' if rule_id else 'CREATE', after=dict(row))
        return dict(row)

    # ── Audit log access ───────────────────────────────────────────────────────

    def get_audit_log(
        self,
        conn,
        client_id: int = 1,
        entity_type: Optional[str] = None,
        entity_id: Optional[int] = None,
        limit: int = 100,
        offset: int = 0,
    ) -> List[Dict]:
        """Fetch admin audit log entries."""
        conditions = []
        params: List[Any] = []

        if entity_type:
            conditions.append('entity_type = %s')
            params.append(entity_type)
        if entity_id:
            conditions.append('entity_id = %s')
            params.append(entity_id)

        where = f"WHERE {' AND '.join(conditions)}" if conditions else ''

        with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
            cur.execute(
                f"""
                SELECT al.*, au.username AS admin_username
                FROM admin_audit_log al
                LEFT JOIN admin_users au ON au.id = al.admin_user_id
                {where}
                ORDER BY al.created_at DESC
                LIMIT %s OFFSET %s
                """,
                [*params, limit, offset],
            )
            rows = cur.fetchall()

        return [dict(r) for r in rows]


# =====================================================
# SCHEMA MIGRATION HELPERS
# =====================================================

ADMIN_SERVICE_MIGRATIONS = """
-- admin_audit_log: tracks all admin mutations
CREATE TABLE IF NOT EXISTS admin_audit_log (
    id SERIAL PRIMARY KEY,
    admin_user_id INTEGER REFERENCES admin_users(id) ON DELETE SET NULL,
    entity_type VARCHAR(60) NOT NULL,
    entity_id INTEGER,
    action VARCHAR(30) NOT NULL,
    before_json JSONB,
    after_json JSONB,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_audit_log_entity ON admin_audit_log(entity_type, entity_id);
CREATE INDEX IF NOT EXISTS idx_audit_log_admin  ON admin_audit_log(admin_user_id);
CREATE INDEX IF NOT EXISTS idx_audit_log_action ON admin_audit_log(action);
CREATE INDEX IF NOT EXISTS idx_audit_log_ts     ON admin_audit_log(created_at DESC);

-- bundle_rules: defines hotel+cab+sightseeing bundles
CREATE TABLE IF NOT EXISTS bundle_rules (
    id SERIAL PRIMARY KEY,
    client_id INTEGER NOT NULL DEFAULT 1 REFERENCES clients(id) ON DELETE CASCADE,
    region_id INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    rule_name VARCHAR(150) NOT NULL,
    rule_config JSONB NOT NULL DEFAULT '{}',
    discount_percent DECIMAL(5,2) NOT NULL DEFAULT 0,
    active BOOLEAN NOT NULL DEFAULT TRUE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_bundle_rules_client ON bundle_rules(client_id, region_id);

-- Cabs table additions (if not present)
DO $$
BEGIN
    IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='cabs' AND column_name='cab_type') THEN
        ALTER TABLE cabs ADD COLUMN cab_type VARCHAR(40) DEFAULT 'SEDAN';
    END IF;
    IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='cabs' AND column_name='rate_per_km') THEN
        ALTER TABLE cabs ADD COLUMN rate_per_km DECIMAL(10,2) DEFAULT 0;
    END IF;
    IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='cabs' AND column_name='rate_per_day') THEN
        ALTER TABLE cabs ADD COLUMN rate_per_day DECIMAL(10,2) DEFAULT 0;
    END IF;
    IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='cabs' AND column_name='rate_flat') THEN
        ALTER TABLE cabs ADD COLUMN rate_flat DECIMAL(10,2) DEFAULT 0;
    END IF;
    IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='cabs' AND column_name='pricing_type') THEN
        ALTER TABLE cabs ADD COLUMN pricing_type VARCHAR(20) DEFAULT 'per_vehicle';
    END IF;
END $$;
"""


def run_admin_service_migrations(conn) -> None:
    """Run admin service schema migrations. Call once on startup."""
    try:
        with conn.cursor() as cur:
            cur.execute(ADMIN_SERVICE_MIGRATIONS)
        conn.commit()
        logger.info("admin_service migrations applied.")
    except Exception as e:
        conn.rollback()
        logger.error(f"admin_service migration failed: {e}")


# =====================================================
# SINGLETON
# =====================================================

_admin_service: Optional[AdminService] = None


def get_admin_service() -> AdminService:
    """Return singleton AdminService instance."""
    global _admin_service
    if _admin_service is None:
        _admin_service = AdminService()
    return _admin_service