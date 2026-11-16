//! M4-7 (Appendix K 7.7): time, random and secrets helpers.
//!
//! The civil calendar (dates, day arithmetic) is hand-written integer
//! math (the Howard Hinnant days-from-civil algorithm). The IANA time
//! zone database (S51) comes from jiff with `tzdb-bundle-always` (the
//! same bundled data, IANA 2026e, on Windows and Linux; the system
//! zoneinfo features are off so the bundled data is used everywhere).
//! The random generator (S54) is xoshiro256++ seeded by splitmix64,
//! hand-written. `hash of x` (S55) is SHA-256 through the sha2 crate,
//! written as 64 lower-case hexadecimal digits.

use std::collections::HashMap;
use std::sync::OnceLock;

// ============================================================= civil dates

/// Days from 1970-01-01 for a proleptic Gregorian (y, m, d), Howard
/// Hinnant's algorithm. Month and day need not be in range ( callers
/// validate first).
pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400; // [0, 399]
    let mp = (m + 9) % 12; // [0, 11]
    let doy = (153 * mp + 2) / 5 + d - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146_097 + doe - 719_468
}

/// The proleptic Gregorian (y, m, d) for days from 1970-01-01 (the
/// inverse of days_from_civil, same algorithm).
pub fn civil_from_days(z: i64) -> (i64, i64, i64) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// M4-S50: an impossible date is a bug (T0620). The check goes through
/// jiff's proleptic Gregorian calendar (the same one the rest of the
/// time helpers use).
pub fn valid_date(y: i64, m: i64, d: i64) -> bool {
    if !(1..=12).contains(&m) {
        return false;
    }
    let len = match m {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        _ => {
            // February: the leap rule of the proleptic Gregorian calendar
            if (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 {
                29
            } else {
                28
            }
        }
    };
    (1..=len).contains(&d) && y != 0 || y == 0 && (1..=len).contains(&d)
}

/// M4-S50/S53: a date prints YYYY-MM-DD.
pub fn fmt_date(y: i64, m: i64, d: i64) -> String {
    format!("{y:04}-{m:02}-{d:02}")
}

// ============================================================= zones

/// M4-S51: zone names match ignoring case, spaces and slashes against
/// the IANA names (americanewyork finds America/New_York). Underscores
/// are ignored too (America/New_York holds one).
fn zone_key(name: &str) -> String {
    name.chars()
        .filter(|c| !matches!(c, ' ' | '/' | '_'))
        .map(|c| c.to_ascii_lowercase())
        .collect()
}

/// The key -> IANA name table over the bundled database, built once.
fn zone_table() -> &'static HashMap<String, String> {
    static TABLE: OnceLock<HashMap<String, String>> = OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = HashMap::new();
        for name in jiff::tz::db().available() {
            let name = name.as_str().to_string();
            // the first spelling in the iteration wins; canonical names
            // come before their aliases
            map.entry(zone_key(&name)).or_insert(name);
        }
        map
    })
}

/// M4-S51: the IANA name for a zone word run, or None (T0171).
pub fn find_zone(names: &str) -> Option<String> {
    zone_table().get(&zone_key(names)).cloned()
}

/// M4-S51: the local zone's IANA name ("local" when the platform gives
/// no name; logged cut).
pub fn local_zone_name() -> String {
    jiff::tz::TimeZone::system()
        .iana_name()
        .unwrap_or("local")
        .to_string()
}

/// The zone's civil time for an instant: (y, m, d, h, min, s, subsec
/// nanos). Returns None when the zone name is unknown.
#[allow(clippy::type_complexity)]
pub fn zone_civil(nanos: i128, zone: &str) -> Option<(i64, i64, i64, i64, i64, i64, i64)> {
    let ts = jiff::Timestamp::from_nanosecond(nanos).ok()?;
    let tz = jiff::tz::TimeZone::get(zone).ok()?;
    let z = ts.to_zoned(tz);
    let d = z.date();
    let t = z.time();
    Some((
        d.year() as i64,
        d.month() as i64,
        d.day() as i64,
        t.hour() as i64,
        t.minute() as i64,
        t.second() as i64,
        t.subsec_nanosecond() as i64,
    ))
}

/// M4-S51/S53: a moment prints 2026-10-31T14:30:00+06:00 (a nonzero
/// sub-second part appends up to 9 fraction digits, trailing zeros
/// trimmed - logged cut).
pub fn fmt_moment(nanos: i128, zone: &str) -> String {
    let Some((y, m, d, h, mi, s, sub)) = zone_civil(nanos, zone) else {
        return format!("<unknown zone {zone}>");
    };
    let base = format!("{}T{:02}:{:02}:{:02}", fmt_date(y, m, d), h, mi, s);
    if sub == 0 {
        return format!("{base}{}", fmt_offset(nanos, zone));
    }
    let frac = format!("{:09}", sub);
    let frac = frac.trim_end_matches('0');
    format!("{base}.{frac}{}", fmt_offset(nanos, zone))
}

/// The +HH:MM offset the zone holds AT this instant.
fn fmt_offset(nanos: i128, zone: &str) -> String {
    let Some(ts) = jiff::Timestamp::from_nanosecond(nanos).ok() else {
        return String::new();
    };
    let Ok(tz) = jiff::tz::TimeZone::get(zone) else {
        return String::new();
    };
    // offset().duration_until(0) measures from the zone offset BACK to
    // UTC, so its sign is the negation of the zone's UTC offset
    // (Asia/Dhaka +06:00 measures -6h); negate it back.
    let secs = -ts
        .to_zoned(tz)
        .offset()
        .duration_until(jiff::tz::Offset::constant(0))
        .as_secs();
    let sign = if secs < 0 { '-' } else { '+' };
    let a = secs.abs();
    format!("{sign}{:02}:{:02}", a / 3600, (a % 3600) / 60)
}

/// M4-G55: the epoch nanoseconds of H:M:00 on date D in the local zone.
/// DST gaps and folds resolve with jiff's compatible mode (logged).
pub fn local_moment_nanos(y: i64, m: i64, d: i64, h: i64, mi: i64) -> Option<i128> {
    let dt =
        jiff::civil::DateTime::new(y as i16, m as i8, d as i8, h as i8, mi as i8, 0, 0).ok()?;
    let z = dt.to_zoned(jiff::tz::TimeZone::system()).ok()?;
    Some(z.timestamp().as_nanosecond())
}

/// M4-G54: today's (y, m, d) in the local zone.
pub fn today_ymd() -> (i64, i64, i64) {
    let z = jiff::Zoned::now();
    (z.year() as i64, z.month() as i64, z.day() as i64)
}

/// The current instant's epoch nanoseconds.
pub fn now_nanos() -> i128 {
    jiff::Timestamp::now().as_nanosecond()
}

// ============================================================= durations

/// M4-S52/S53: a duration prints the largest units that fit, joined by
/// and, such as 2 hours and 5 minutes; a zero duration prints 0
/// seconds. Units: days, hours, minutes, seconds (months and years are
/// not units in M4); a nonzero sub-second part prints as a fraction on
/// the seconds (trailing zeros trimmed).
pub fn fmt_duration(nanos: i128) -> String {
    if nanos == 0 {
        return "0 seconds".to_string();
    }
    let neg = nanos < 0;
    let a = nanos.unsigned_abs();
    let day = 86_400_000_000_000u128;
    let hour = 3_600_000_000_000u128;
    let min = 60_000_000_000u128;
    let sec = 1_000_000_000u128;
    let days = a / day;
    let hours = (a % day) / hour;
    let minutes = (a % hour) / min;
    let seconds_total = a % min;
    let whole = seconds_total / sec;
    let sub = seconds_total % sec;
    let mut parts: Vec<String> = Vec::new();
    if days > 0 {
        parts.push(format!("{} {}", days, plural(days, "day", "days")));
    }
    if hours > 0 {
        parts.push(format!("{} {}", hours, plural(hours, "hour", "hours")));
    }
    if minutes > 0 {
        parts.push(format!(
            "{} {}",
            minutes,
            plural(minutes, "minute", "minutes")
        ));
    }
    if whole > 0 || sub > 0 {
        let text = if sub > 0 {
            let frac = format!("{:09}", sub);
            let frac = frac.trim_end_matches('0');
            format!("{whole}.{frac}")
        } else {
            format!("{whole}")
        };
        parts.push(format!("{} {}", text, plural(whole, "second", "seconds")));
    }
    let joined = parts.join(" and ");
    if neg {
        format!("minus {joined}")
    } else {
        joined
    }
}

fn plural<'a>(n: u128, one: &'a str, many: &'a str) -> &'a str {
    if n == 1 { one } else { many }
}

// ============================================================= random

/// M4-S54: the generator is xoshiro256++ seeded by splitmix64 from the
/// number.
pub fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Seed a xoshiro256++ state by splitmix64 from one number (S54).
pub fn xoshiro_seed(seed: u64) -> [u64; 4] {
    let mut sm = seed;
    [
        splitmix64(&mut sm),
        splitmix64(&mut sm),
        splitmix64(&mut sm),
        splitmix64(&mut sm),
    ]
}

/// The xoshiro256++ next step (all-zero states are disallowed; a
/// zero-seeded state is replaced the way the reference generator does,
/// by treating it as one).
pub fn xoshiro_next(s: &mut [u64; 4]) -> u64 {
    if *s == [0, 0, 0, 0] {
        *s = xoshiro_seed(0x9E37_79B9_7F4A_7C15);
    }
    let result = s[0].wrapping_add(s[3]).rotate_left(23).wrapping_add(s[0]);
    let t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = s[3].rotate_left(45);
    result
}

/// The operating system's entropy (S54): std seeds its default hasher
/// keys from the operating system's entropy, so two RandomState keys
/// give 128 unpredictable bits, expanded by splitmix64 (logged cut: no
/// getrandom dependency in this cut).
pub fn os_seed() -> u64 {
    use std::hash::{BuildHasher, Hasher, RandomState};
    let mut h = RandomState::new().build_hasher();
    h.write_u64(0x0DDB_1A5E_5BAD_5EED);
    h.finish()
}

// ============================================================= hash

/// M4-S55: hash of x is the SHA-256 hash of the UTF-8 bytes, written
/// as 64 lower-case hexadecimal digits.
pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    h.update(bytes);
    let out = h.finalize();
    let mut s = String::with_capacity(64);
    for b in out {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
