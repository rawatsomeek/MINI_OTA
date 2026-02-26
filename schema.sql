-- ============================================================
-- schema.sql — VoyageAI / Global Calc OTA Platform
-- Version 5.1 — Full Schema
-- Safe to run multiple times (all IF NOT EXISTS)
-- Deploy this file alongside app.py on Render
-- ============================================================

-- ============================================================
-- 1. CLIENTS
-- ============================================================
CREATE TABLE IF NOT EXISTS clients (
    id                 SERIAL PRIMARY KEY,
    name               VARCHAR(150) NOT NULL,
    code               VARCHAR(30)  NOT NULL UNIQUE,
    contact_email      VARCHAR(200),
    contact_phone      VARCHAR(30),
    currency_default   VARCHAR(10)  NOT NULL DEFAULT 'INR',
    active             BOOLEAN      NOT NULL DEFAULT TRUE,
    created_at         TIMESTAMP    DEFAULT CURRENT_TIMESTAMP,
    updated_at         TIMESTAMP    DEFAULT CURRENT_TIMESTAMP
);

-- Default client seed
INSERT INTO clients (id, name, code, currency_default)
VALUES (1, 'AKS Hospitality', 'aks-hospitality', 'INR')
ON CONFLICT (id) DO NOTHING;

-- ============================================================
-- 2. ADMIN USERS
-- ============================================================
CREATE TABLE IF NOT EXISTS admin_users (
    id            SERIAL PRIMARY KEY,
    username      VARCHAR(100) NOT NULL UNIQUE,
    password_hash VARCHAR(255),
    pin_hash      VARCHAR(255),
    created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_admin_users_username ON admin_users(username);

-- ============================================================
-- 3. WEBAUTHN / PASSKEY CREDENTIALS
-- ============================================================
CREATE TABLE IF NOT EXISTS webauthn_credentials (
    id             SERIAL PRIMARY KEY,
    admin_user_id  INTEGER NOT NULL REFERENCES admin_users(id) ON DELETE CASCADE,
    credential_id  BYTEA   NOT NULL UNIQUE,
    public_key     BYTEA   NOT NULL,
    sign_count     INTEGER NOT NULL DEFAULT 0,
    device_name    VARCHAR(100),
    created_at     TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_webauthn_admin ON webauthn_credentials(admin_user_id);

-- ============================================================
-- 4. ADMIN REQUESTS (signup / forgot password / forgot username)
-- ============================================================
CREATE TABLE IF NOT EXISTS admin_requests (
    id                     SERIAL PRIMARY KEY,
    request_type           VARCHAR(20) NOT NULL DEFAULT 'signup'
                               CHECK (request_type IN ('signup', 'forgot_password', 'forgot_username')),
    username               VARCHAR(100),
    password_hash          VARCHAR(255),
    pin_hash               VARCHAR(255),
    company                VARCHAR(200),
    email                  VARCHAR(200) NOT NULL,
    full_name              VARCHAR(200),
    phone                  VARCHAR(30),
    status                 VARCHAR(20) NOT NULL DEFAULT 'pending'
                               CHECK (status IN ('pending', 'approved', 'rejected', 'expired')),
    approve_token          VARCHAR(128) NOT NULL UNIQUE,
    reject_token           VARCHAR(128) NOT NULL UNIQUE,
    reset_token            VARCHAR(128) UNIQUE,
    reset_token_expires_at TIMESTAMP,
    expires_at             TIMESTAMP   NOT NULL,
    processed_at           TIMESTAMP,
    owner_note             TEXT,
    created_at             TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at             TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_admin_requests_approve_token ON admin_requests(approve_token);
CREATE INDEX IF NOT EXISTS idx_admin_requests_reject_token  ON admin_requests(reject_token);
CREATE INDEX IF NOT EXISTS idx_admin_requests_reset_token   ON admin_requests(reset_token) WHERE reset_token IS NOT NULL;
CREATE INDEX IF NOT EXISTS idx_admin_requests_email         ON admin_requests(email);
CREATE INDEX IF NOT EXISTS idx_admin_requests_status        ON admin_requests(status);

-- ============================================================
-- 5. AGENTS (simple agent/B2B login)
-- ============================================================
CREATE TABLE IF NOT EXISTS agents (
    id         SERIAL PRIMARY KEY,
    name       VARCHAR(100) NOT NULL UNIQUE,
    password   VARCHAR(255),
    email      VARCHAR(200),
    phone      VARCHAR(30),
    company    VARCHAR(200),
    active     BOOLEAN   NOT NULL DEFAULT TRUE,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_agents_name ON agents(name);

-- ============================================================
-- 6. REGIONS
-- ============================================================
CREATE TABLE IF NOT EXISTS regions (
    id               SERIAL PRIMARY KEY,
    client_id        INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    name             VARCHAR(150) NOT NULL,
    currency         VARCHAR(10)  NOT NULL DEFAULT 'INR',
    is_domestic      BOOLEAN      NOT NULL DEFAULT TRUE,
    service_percent  DECIMAL(6,2) NOT NULL DEFAULT 15,
    booking_percent  DECIMAL(6,2) NOT NULL DEFAULT 12,
    active           BOOLEAN      NOT NULL DEFAULT TRUE,
    created_at       TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at       TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_regions_client ON regions(client_id, active);

-- ============================================================
-- 7. DESTINATIONS
-- ============================================================
CREATE TABLE IF NOT EXISTS destinations (
    id                   SERIAL PRIMARY KEY,
    client_id            INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    region_id            INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    name                 VARCHAR(150) NOT NULL,
    internal_name        VARCHAR(150) NOT NULL,
    display_name         VARCHAR(200),
    destination_type     VARCHAR(30)  NOT NULL DEFAULT 'CITY'
                             CHECK (destination_type IN (
                                 'CITY','HILL_STATION','BEACH','RELIGIOUS',
                                 'ADVENTURE','WILDLIFE','HERITAGE','OTHER'
                             )),
    is_special           BOOLEAN      NOT NULL DEFAULT FALSE,
    base_rate            DECIMAL(12,2) NOT NULL DEFAULT 0,
    per_day_rate         DECIMAL(12,2) NOT NULL DEFAULT 0,
    four_by_four_rate    DECIMAL(12,2) NOT NULL DEFAULT 0,
    free_sightseeing_days INTEGER      NOT NULL DEFAULT 0,
    description          TEXT         DEFAULT '',
    best_time            VARCHAR(200)  DEFAULT '',
    duration_days        INTEGER       DEFAULT NULL,
    highlights           JSONB         DEFAULT '[]',
    active               BOOLEAN       NOT NULL DEFAULT TRUE,
    created_at           TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at           TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (client_id, region_id, internal_name)
);

CREATE INDEX IF NOT EXISTS idx_destinations_client  ON destinations(client_id, active);
CREATE INDEX IF NOT EXISTS idx_destinations_region  ON destinations(region_id);

-- ============================================================
-- 8. HOTELS
-- ============================================================
CREATE TABLE IF NOT EXISTS hotels (
    id                      SERIAL PRIMARY KEY,
    client_id               INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    region_id               INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    destination_id          INTEGER REFERENCES destinations(id) ON DELETE SET NULL,
    name                    VARCHAR(200) NOT NULL,
    internal_name           VARCHAR(200) NOT NULL,
    display_name            VARCHAR(250),
    hotel_type              VARCHAR(30)  NOT NULL DEFAULT 'STANDARD'
                                CHECK (hotel_type IN (
                                    'STANDARD','BOUTIQUE','RESORT','HERITAGE','BUDGET','LUXURY'
                                )),
    star_rating             INTEGER      NOT NULL DEFAULT 3,
    location                VARCHAR(300) DEFAULT '',
    city                    VARCHAR(150) DEFAULT '',
    address                 TEXT         DEFAULT '',
    description             TEXT         DEFAULT '',
    amenities               TEXT[]       DEFAULT ARRAY[]::TEXT[],
    images                  TEXT         DEFAULT '[]',
    sharing_type            VARCHAR(30)  DEFAULT 'TWIN',
    sharing_capacity        INTEGER      NOT NULL DEFAULT 2,
    custom_sharing_name     VARCHAR(100) DEFAULT '',
    is_kasol                BOOLEAN      NOT NULL DEFAULT FALSE,
    extra_mattress_rate     DECIMAL(12,2) NOT NULL DEFAULT 0,
    extra_mattress_child_rate DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_age_limit         INTEGER       NOT NULL DEFAULT 12,
    adult_rate_peak         DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate_peak         DECIMAL(12,2) NOT NULL DEFAULT 0,
    adult_rate_off          DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate_off          DECIMAL(12,2) NOT NULL DEFAULT 0,
    active                  BOOLEAN      NOT NULL DEFAULT TRUE,
    created_at              TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at              TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (client_id, region_id, internal_name)
);

CREATE INDEX IF NOT EXISTS idx_hotels_client      ON hotels(client_id, active);
CREATE INDEX IF NOT EXISTS idx_hotels_region      ON hotels(region_id);
CREATE INDEX IF NOT EXISTS idx_hotels_destination ON hotels(destination_id);

-- ============================================================
-- 9. CABS
-- ============================================================
CREATE TABLE IF NOT EXISTS cabs (
    id            SERIAL PRIMARY KEY,
    client_id     INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    region_id     INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    name          VARCHAR(150) NOT NULL,
    internal_name VARCHAR(150) NOT NULL,
    display_name  VARCHAR(200),
    cab_type      VARCHAR(40)   DEFAULT 'SEDAN',
    seat_capacity INTEGER       NOT NULL DEFAULT 4,
    rate_per_km   DECIMAL(10,2) DEFAULT 0,
    rate_per_day  DECIMAL(10,2) DEFAULT 0,
    rate_flat     DECIMAL(10,2) DEFAULT 0,
    pricing_type  VARCHAR(20)   DEFAULT 'per_vehicle',
    active        BOOLEAN       NOT NULL DEFAULT TRUE,
    created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (client_id, region_id, internal_name)
);

CREATE INDEX IF NOT EXISTS idx_cabs_client ON cabs(client_id, active);
CREATE INDEX IF NOT EXISTS idx_cabs_region ON cabs(region_id);

-- ============================================================
-- 10. CAB DESTINATION RATES
-- ============================================================
CREATE TABLE IF NOT EXISTS cab_destination_rates (
    id             SERIAL PRIMARY KEY,
    client_id      INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    cab_id         INTEGER NOT NULL REFERENCES cabs(id) ON DELETE CASCADE,
    destination_id INTEGER NOT NULL REFERENCES destinations(id) ON DELETE CASCADE,
    rate           DECIMAL(12,2) NOT NULL DEFAULT 0,
    override_rate  DECIMAL(12,2),
    created_at     TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at     TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (client_id, cab_id, destination_id)
);

CREATE INDEX IF NOT EXISTS idx_cab_dest_rates_cab  ON cab_destination_rates(cab_id);
CREATE INDEX IF NOT EXISTS idx_cab_dest_rates_dest ON cab_destination_rates(destination_id);

-- ============================================================
-- 11. TRANSPORTS (flights, buses, trains as inventory items)
-- ============================================================
CREATE TABLE IF NOT EXISTS transports (
    id                  SERIAL PRIMARY KEY,
    client_id           INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    region_id           INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    name                VARCHAR(200) NOT NULL,
    internal_name       VARCHAR(200),
    display_name        VARCHAR(250),
    transport_type      VARCHAR(30) NOT NULL DEFAULT 'BUS',
    seat_capacity       INTEGER     NOT NULL DEFAULT 40,
    adult_rate_peak     DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate_peak     DECIMAL(12,2) NOT NULL DEFAULT 0,
    peak_pricing_type   VARCHAR(20)   NOT NULL DEFAULT 'per_person',
    adult_rate_off      DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate_off      DECIMAL(12,2) NOT NULL DEFAULT 0,
    off_pricing_type    VARCHAR(20)   NOT NULL DEFAULT 'per_person',
    trip_type           VARCHAR(20)   NOT NULL DEFAULT 'one_way'
                            CHECK (trip_type IN ('one_way', 'return', 'both')),
    active              BOOLEAN       NOT NULL DEFAULT TRUE,
    created_at          TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at          TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_transports_client ON transports(client_id, active);
CREATE INDEX IF NOT EXISTS idx_transports_region ON transports(region_id);

-- ============================================================
-- 12. ADDONS (sightseeing, activities, meals, etc.)
-- ============================================================
CREATE TABLE IF NOT EXISTS addons (
    id            SERIAL PRIMARY KEY,
    client_id     INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    region_id     INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    name          VARCHAR(200) NOT NULL,
    internal_name VARCHAR(200) NOT NULL,
    display_name  VARCHAR(250),
    addon_type    VARCHAR(50)  NOT NULL DEFAULT 'SIGHTSEEING',
    pricing_type  VARCHAR(30)  NOT NULL DEFAULT 'per_person'
                      CHECK (pricing_type IN ('per_person','per_booking','per_night','per_vehicle')),
    rate_peak     DECIMAL(12,2) NOT NULL DEFAULT 0,
    rate_off      DECIMAL(12,2) NOT NULL DEFAULT 0,
    description   TEXT          DEFAULT '',
    active        BOOLEAN       NOT NULL DEFAULT TRUE,
    created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    UNIQUE (client_id, region_id, internal_name)
);

CREATE INDEX IF NOT EXISTS idx_addons_client ON addons(client_id, active);
CREATE INDEX IF NOT EXISTS idx_addons_region ON addons(region_id);

-- ============================================================
-- 13. GLOBAL RULES (per client)
-- ============================================================
CREATE TABLE IF NOT EXISTS global_rules (
    id                   SERIAL PRIMARY KEY,
    client_id            INTEGER NOT NULL UNIQUE REFERENCES clients(id) ON DELETE CASCADE,
    service_charge       DECIMAL(6,2) NOT NULL DEFAULT 15,
    booking_charge       DECIMAL(6,2) NOT NULL DEFAULT 12,
    tax                  DECIMAL(6,2) NOT NULL DEFAULT 5,
    default_margin       DECIMAL(6,2) NOT NULL DEFAULT 20,
    default_cancellation TEXT         DEFAULT '',
    created_at           TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at           TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Ensure default global_rules row exists for client 1
INSERT INTO global_rules (client_id) VALUES (1) ON CONFLICT (client_id) DO NOTHING;

-- ============================================================
-- 14. HOTEL PRICING RANGES (date-based overrides)
-- ============================================================
CREATE TABLE IF NOT EXISTS hotel_pricing_ranges (
    id          SERIAL PRIMARY KEY,
    client_id   INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    hotel_id    INTEGER NOT NULL REFERENCES hotels(id) ON DELETE CASCADE,
    label       VARCHAR(100) DEFAULT '',
    start_date  DATE NOT NULL,
    end_date    DATE NOT NULL,
    adult_rate  DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate  DECIMAL(12,2) NOT NULL DEFAULT 0,
    created_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at  TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_hotel_pricing_ranges ON hotel_pricing_ranges(hotel_id, start_date, end_date);

-- ============================================================
-- 15. TRANSPORT PRICING RANGES
-- ============================================================
CREATE TABLE IF NOT EXISTS transport_pricing_ranges (
    id            SERIAL PRIMARY KEY,
    client_id     INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    transport_id  INTEGER NOT NULL REFERENCES transports(id) ON DELETE CASCADE,
    label         VARCHAR(100) DEFAULT '',
    start_date    DATE NOT NULL,
    end_date      DATE NOT NULL,
    adult_rate    DECIMAL(12,2) NOT NULL DEFAULT 0,
    child_rate    DECIMAL(12,2) NOT NULL DEFAULT 0,
    pricing_type  VARCHAR(20)   NOT NULL DEFAULT 'per_person',
    created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_transport_pricing_ranges ON transport_pricing_ranges(transport_id, start_date, end_date);

-- ============================================================
-- 16. ADDON PRICING RANGES
-- ============================================================
CREATE TABLE IF NOT EXISTS addon_pricing_ranges (
    id         SERIAL PRIMARY KEY,
    client_id  INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    addon_id   INTEGER NOT NULL REFERENCES addons(id) ON DELETE CASCADE,
    label      VARCHAR(100) DEFAULT '',
    start_date DATE NOT NULL,
    end_date   DATE NOT NULL,
    rate       DECIMAL(12,2) NOT NULL DEFAULT 0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_addon_pricing_ranges ON addon_pricing_ranges(addon_id, start_date, end_date);

-- ============================================================
-- 17. PRICING RULES (dynamic rule engine)
-- ============================================================
CREATE TABLE IF NOT EXISTS pricing_rules (
    id              SERIAL PRIMARY KEY,
    client_id       INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    name            VARCHAR(200) NOT NULL,
    description     TEXT         DEFAULT '',
    entity_type     VARCHAR(50)  NOT NULL DEFAULT 'global',
    entity_id       INTEGER,
    conditions_json JSONB        NOT NULL DEFAULT '{}',
    actions_json    JSONB        NOT NULL DEFAULT '{}',
    priority        INTEGER      NOT NULL DEFAULT 10,
    stackable       BOOLEAN      NOT NULL DEFAULT FALSE,
    active          BOOLEAN      NOT NULL DEFAULT TRUE,
    created_at      TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at      TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_pricing_rules_client ON pricing_rules(client_id, entity_type, active);
CREATE INDEX IF NOT EXISTS idx_pricing_rules_entity ON pricing_rules(entity_type, entity_id);

-- ============================================================
-- 18. BUNDLE RULES
-- ============================================================
CREATE TABLE IF NOT EXISTS bundle_rules (
    id               SERIAL PRIMARY KEY,
    client_id        INTEGER NOT NULL DEFAULT 1 REFERENCES clients(id) ON DELETE CASCADE,
    region_id        INTEGER NOT NULL REFERENCES regions(id) ON DELETE CASCADE,
    rule_name        VARCHAR(150) NOT NULL,
    rule_config      JSONB        NOT NULL DEFAULT '{}',
    discount_percent DECIMAL(5,2) NOT NULL DEFAULT 0,
    active           BOOLEAN      NOT NULL DEFAULT TRUE,
    created_at       TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at       TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_bundle_rules_client ON bundle_rules(client_id, region_id);

-- ============================================================
-- 19. BOOKINGS
-- ============================================================
CREATE TABLE IF NOT EXISTS bookings (
    id                      SERIAL PRIMARY KEY,
    client_id               INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
    internal_ref            VARCHAR(50) NOT NULL UNIQUE,
    flight_pnr              VARCHAR(20),
    hotel_confirmation      VARCHAR(50),
    flight_offer_id         VARCHAR(100),
    hotel_offer_id          VARCHAR(100),
    traveler_details        JSONB,
    flight_booking_response JSONB,
    hotel_booking_response  JSONB,
    status                  VARCHAR(30) NOT NULL DEFAULT 'confirmed',
    created_at              TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at              TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_bookings_client ON bookings(client_id);
CREATE INDEX IF NOT EXISTS idx_bookings_ref    ON bookings(internal_ref);

-- ============================================================
-- 20. TRENDING PACKAGES (homepage featured packages)
-- ============================================================
CREATE TABLE IF NOT EXISTS trending_packages (
    id             SERIAL PRIMARY KEY,
    client_id      INTEGER NOT NULL DEFAULT 1,
    name           VARCHAR(200) NOT NULL,
    tagline        VARCHAR(300) DEFAULT '',
    description    TEXT         DEFAULT '',
    image_url      TEXT         DEFAULT '',
    gallery_images JSONB        DEFAULT '[]',
    duration_days  INTEGER      DEFAULT NULL,
    price_from     NUMERIC(12,2) DEFAULT NULL,
    currency       VARCHAR(10)  DEFAULT 'INR',
    included_items JSONB        DEFAULT '[]',
    display_order  INTEGER      DEFAULT 0,
    active         BOOLEAN      NOT NULL DEFAULT TRUE,
    deleted        BOOLEAN      NOT NULL DEFAULT FALSE,
    created_at     TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at     TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_trending_packages_client ON trending_packages(client_id, active, deleted);

-- ============================================================
-- 21. ADMIN AUDIT LOG
-- ============================================================
CREATE TABLE IF NOT EXISTS admin_audit_log (
    id            SERIAL PRIMARY KEY,
    admin_user_id INTEGER REFERENCES admin_users(id) ON DELETE SET NULL,
    entity_type   VARCHAR(60) NOT NULL,
    entity_id     INTEGER,
    action        VARCHAR(30) NOT NULL,
    before_json   JSONB,
    after_json    JSONB,
    created_at    TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX IF NOT EXISTS idx_audit_log_entity ON admin_audit_log(entity_type, entity_id);
CREATE INDEX IF NOT EXISTS idx_audit_log_admin  ON admin_audit_log(admin_user_id);
CREATE INDEX IF NOT EXISTS idx_audit_log_action ON admin_audit_log(action);
CREATE INDEX IF NOT EXISTS idx_audit_log_ts     ON admin_audit_log(created_at DESC);

-- ============================================================
-- 22. SCHEMA VERSION TRACKING
-- ============================================================
CREATE TABLE IF NOT EXISTS schema_versions (
    id         SERIAL PRIMARY KEY,
    version    VARCHAR(20) NOT NULL,
    applied_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    notes      TEXT
);

INSERT INTO schema_versions (version, notes)
VALUES ('5.1', 'Full schema generated from app.py — VoyageAI OTA Platform')
ON CONFLICT DO NOTHING;

-- ============================================================
-- END OF SCHEMA
-- ============================================================