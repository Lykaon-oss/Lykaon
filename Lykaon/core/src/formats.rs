//! M4-6 (Appendix K 7.6): the five formats. Every reader builds the ONE
//! ordered tree below (`FVal`; objects keep their key order because a
//! map decode keeps the file's key order, M4-S45), and the kind-directed
//! decode S42..S45 is written once against that tree. Encoding is the
//! reverse (S46), driven by the value itself. Decoding never runs code
//! and never reads past a nesting depth of 256 (M4-S48) - the depth is
//! checked when every container is opened, in the reader and again in
//! the decode walk.
//!
//! All parsers are hand-written (json too, to own the depth limit and
//! the key order). Failures are shape failures the caller reports (the
//! file sentences fail anonymously - the logged Ask precedent), so this
//! module returns plain Results.
//!
//! Subset lines logged in LYKAON_DEVIATIONS.md: toml takes the S47 shapes
//! (tables and arrays of tables, inline tables for maps, basic and
//! literal strings, numbers, true/false; no dates, no multi-line scalar
//! constructs); yaml is the block-style 1.2 core subset (no anchors, no
//! tags, no multi-document files, no flow style; lists may sit at the
//! same indentation as their keys, one common spelling); xml reads a
//! record from an element named as the kind, a text part is the
//! element's content, a list part repeats its element, attributes are
//! ignored, and xml holds no enumeration value and no top-level list
//! (nothing in the doc gives them a spelling); csv takes RFC 4180 cells
//! and coerces them to the part kinds.

use crate::sem::{Kind, Value};

/// The five format words (M4-G53), in their sentence spelling.
pub const FORMAT_WORDS: [&str; 5] = ["json", "toml", "yaml", "xml", "csv"];

/// M4-S48: the deepest nested container read or written.
pub const MAX_DEPTH: usize = 256;

/// The parsed-or-written shape shared by all five formats.
#[derive(Clone, Debug)]
pub enum FVal {
    /// An object (json object, toml table or inline table, yaml map,
    /// xml element's children). The source's key order is kept for a
    /// map decode (M4-S45).
    Obj(Vec<(String, FVal)>),
    /// An array (json array, toml array, yaml list, repeated xml
    /// elements under one name).
    Arr(Vec<FVal>),
    Str(String),
    /// Every number; a whole part checks "no fraction, 64-bit range"
    /// at decode time (M4-S44).
    Num(f64),
    Bool(bool),
    Null,
}

// ------------------------------------------------------------------
// small shared helpers

fn as_whole(n: f64) -> Option<i64> {
    if n.is_finite() && n.fract() == 0.0 && n >= i64::MIN as f64 && n <= i64::MAX as f64 {
        Some(n as i64)
    } else {
        None
    }
}

/// A key holding a part's or a variant's name (M4-S43/S45): the name in
/// lower case with its words joined by _ ("home address" is
/// home_address). The exact spelling is accepted too, so the decode
/// tries both spellings.
fn key_of(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c == ' ' {
                '_'
            } else {
                c.to_ascii_lowercase()
            }
        })
        .collect()
}

fn num_text(d: f64) -> Result<String, ()> {
    // the shortest text that reads back to the same value (M4-S46)
    if let Some(w) = as_whole(d) {
        Ok(w.to_string())
    } else if d.is_finite() {
        Ok(format!("{d}"))
    } else {
        Err(())
    }
}

fn json_string_write(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000C}' => out.push_str("\\f"),
            c => out.push(c),
        }
    }
    out.push('"');
}

// =================================================================
// JSON

pub fn parse_json(s: &str) -> Result<FVal, ()> {
    let mut p = P::new(s.as_bytes());
    p.ws();
    let v = p.json_value(0)?;
    p.ws();
    if p.i != p.b.len() {
        return Err(());
    }
    Ok(v)
}

struct P<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn new(b: &'a [u8]) -> Self {
        P { b, i: 0 }
    }
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\n' | b'\r') {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) -> bool {
        if self.i < self.b.len() && self.b[self.i] == c {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn json_value(&mut self, depth: usize) -> Result<FVal, ()> {
        if depth >= MAX_DEPTH {
            return Err(()); // M4-S48
        }
        match self.b.get(self.i).copied() {
            Some(b'{') => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.eat(b'}') {
                    return Ok(FVal::Obj(items));
                }
                loop {
                    self.ws();
                    let k = match self.json_string()? {
                        FVal::Str(s) => s,
                        _ => return Err(()),
                    };
                    self.ws();
                    if !self.eat(b':') {
                        return Err(());
                    }
                    self.ws();
                    let v = self.json_value(depth + 1)?;
                    items.push((k, v));
                    self.ws();
                    if self.eat(b',') {
                        continue;
                    }
                    if self.eat(b'}') {
                        return Ok(FVal::Obj(items));
                    }
                    return Err(());
                }
            }
            Some(b'[') => {
                self.i += 1;
                let mut items = Vec::new();
                self.ws();
                if self.eat(b']') {
                    return Ok(FVal::Arr(items));
                }
                loop {
                    self.ws();
                    items.push(self.json_value(depth + 1)?);
                    self.ws();
                    if self.eat(b',') {
                        continue;
                    }
                    if self.eat(b']') {
                        return Ok(FVal::Arr(items));
                    }
                    return Err(());
                }
            }
            Some(b'"') => self.json_string(),
            Some(b't') => self.word_fval("true", FVal::Bool(true)),
            Some(b'f') => self.word_fval("false", FVal::Bool(false)),
            Some(b'n') => self.word_fval("null", FVal::Null),
            Some(c) if c == b'-' || c.is_ascii_digit() => self.json_number(),
            _ => Err(()),
        }
    }
    fn word_fval(&mut self, w: &str, v: FVal) -> Result<FVal, ()> {
        if self.b[self.i..].starts_with(w.as_bytes()) {
            self.i += w.len();
            Ok(v)
        } else {
            Err(())
        }
    }
    fn json_number(&mut self) -> Result<FVal, ()> {
        let start = self.i;
        if self.eat(b'-') {}
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            self.i += 1;
        }
        if self.eat(b'.') {
            while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
                self.i += 1;
            }
        }
        if matches!(self.b.get(self.i), Some(b'e') | Some(b'E')) {
            self.i += 1;
            if matches!(self.b.get(self.i), Some(b'+') | Some(b'-')) {
                self.i += 1;
            }
            while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
                self.i += 1;
            }
        }
        let txt = std::str::from_utf8(&self.b[start..self.i]).map_err(|_| ())?;
        if txt.is_empty() {
            return Err(());
        }
        txt.parse::<f64>().map(FVal::Num).map_err(|_| ())
    }
    fn json_string(&mut self) -> Result<FVal, ()> {
        if !self.eat(b'"') {
            return Err(());
        }
        let mut out = String::new();
        loop {
            match self.b.get(self.i).copied() {
                None => return Err(()),
                Some(b'"') => {
                    self.i += 1;
                    return Ok(FVal::Str(out));
                }
                Some(b'\\') => {
                    self.i += 1;
                    match self.b.get(self.i).copied() {
                        Some(b'"') => out.push('"'),
                        Some(b'\\') => out.push('\\'),
                        Some(b'/') => out.push('/'),
                        Some(b'b') => out.push('\u{0008}'),
                        Some(b'f') => out.push('\u{000C}'),
                        Some(b'n') => out.push('\n'),
                        Some(b'r') => out.push('\r'),
                        Some(b't') => out.push('\t'),
                        Some(b'u') => {
                            // surrogate pairs combine into one letter
                            let c = self.hex4()?;
                            let mut ch = char::from_u32(c).ok_or(())?;
                            if (0xD800..=0xDFFF).contains(&c) {
                                // a high surrogate must lead a low one
                                if !(0xD800..=0xDBFF).contains(&c) {
                                    return Err(());
                                }
                                if !self.b[self.i + 1..].starts_with(b"\\u") {
                                    return Err(());
                                }
                                self.i += 2;
                                let c2 = self.hex4()?;
                                if !(0xDC00..=0xDFFF).contains(&c2) {
                                    return Err(());
                                }
                                ch = char::from_u32(0x10000 + ((c - 0xD800) << 10) + (c2 - 0xDC00))
                                    .ok_or(())?;
                            }
                            out.push(ch);
                            continue;
                        }
                        _ => return Err(()),
                    }
                    self.i += 1;
                }
                Some(_) => {
                    // one utf-8 letter at a time
                    let rest = std::str::from_utf8(&self.b[self.i..]).map_err(|_| ())?;
                    let ch = rest.chars().next().ok_or(())?;
                    out.push(ch);
                    self.i += ch.len_utf8();
                }
            }
        }
    }
    fn hex4(&mut self) -> Result<u32, ()> {
        let h =
            std::str::from_utf8(self.b.get(self.i + 1..self.i + 5).ok_or(())?).map_err(|_| ())?;
        self.i += 4;
        u32::from_str_radix(h, 16).map_err(|_| ())
    }
}

pub fn json_decode(s: &str, kind: &Kind) -> Result<Value, ()> {
    let f = parse_json(s)?;
    decode_fval(&f, kind, 0)
}

/// Compact json of a value (M4-S46: no spaces).
pub fn json_compact(v: &Value) -> Result<String, ()> {
    let mut out = String::new();
    json_write(v, false, 0, &mut out)?;
    Ok(out)
}

/// Pretty json: two spaces of indentation (M4-S46, the Save shape;
/// the line feed at the end is the caller's).
pub fn json_pretty(v: &Value) -> Result<String, ()> {
    let mut out = String::new();
    json_write(v, true, 0, &mut out)?;
    Ok(out)
}

fn json_write(vv: &Value, pretty: bool, depth: usize, out: &mut String) -> Result<(), ()> {
    if depth >= MAX_DEPTH {
        return Err(()); // the same cap on the written side (M4-S48)
    }
    match vv {
        Value::Text(s) => {
            json_string_write(s, out);
            Ok(())
        }
        Value::Whole(w) => {
            out.push_str(&w.to_string());
            Ok(())
        }
        Value::Dec(d) => {
            out.push_str(&num_text(*d)?);
            Ok(())
        }
        Value::Boolean(b) => {
            out.push_str(if *b { "true" } else { "false" });
            Ok(())
        }
        Value::Maybe(o) => match o {
            Some(inner) => json_write(inner, pretty, depth + 1, out),
            None => {
                out.push_str("null");
                Ok(())
            }
        },
        Value::Missing => {
            out.push_str("null");
            Ok(())
        }
        Value::List(items) | Value::Set(items) | Value::Queue(items) => {
            out.push('[');
            let mut first = true;
            for v in items {
                if !first {
                    out.push(',');
                    if pretty {
                        out.push(' ');
                    }
                }
                first = false;
                if pretty {
                    out.push('\n');
                    for _ in 0..(depth + 1) * 2 {
                        out.push(' ');
                    }
                }
                json_write(v, pretty, depth + 1, out)?;
            }
            if pretty && !first {
                out.push('\n');
                for _ in 0..depth * 2 {
                    out.push(' ');
                }
            }
            out.push(']');
            Ok(())
        }
        Value::Array(items) => {
            // an array writes its unset slots as null (json has no hole)
            out.push('[');
            let mut first = true;
            for v in items.iter().flatten() {
                if !first {
                    out.push(',');
                    if pretty {
                        out.push(' ');
                    }
                }
                first = false;
                if pretty {
                    out.push('\n');
                    for _ in 0..(depth + 1) * 2 {
                        out.push(' ');
                    }
                }
                json_write(v, pretty, depth + 1, out)?;
            }
            if pretty && !first {
                out.push('\n');
                for _ in 0..depth * 2 {
                    out.push(' ');
                }
            }
            out.push(']');
            Ok(())
        }
        Value::Map(pairs) => {
            out.push('{');
            let mut first = true;
            for (k, v) in pairs {
                let key = match k {
                    Value::Text(t) => t.clone(),
                    _ => return Err(()), // json map keys are text
                };
                if !first {
                    out.push(',');
                    if pretty {
                        out.push(' ');
                    }
                }
                first = false;
                if pretty {
                    out.push('\n');
                    for _ in 0..(depth + 1) * 2 {
                        out.push(' ');
                    }
                }
                json_string_write(&key, out);
                out.push(':');
                if pretty {
                    out.push(' ');
                }
                json_write(v, pretty, depth + 1, out)?;
            }
            if pretty && !first {
                out.push('\n');
                for _ in 0..depth * 2 {
                    out.push(' ');
                }
            }
            out.push('}');
            Ok(())
        }
        Value::Record(_tname, parts) => {
            // records are written with parts in declaration order (S46)
            out.push('{');
            let mut first = true;
            for (pn, pv) in parts {
                if !first {
                    out.push(',');
                    if pretty {
                        out.push(' ');
                    }
                }
                first = false;
                if pretty {
                    out.push('\n');
                    for _ in 0..(depth + 1) * 2 {
                        out.push(' ');
                    }
                }
                json_string_write(&key_of(pn), out);
                out.push(':');
                if pretty {
                    out.push(' ');
                }
                json_write(pv, pretty, depth + 1, out)?;
            }
            if pretty && !first {
                out.push('\n');
                for _ in 0..depth * 2 {
                    out.push(' ');
                }
            }
            out.push('}');
            Ok(())
        }
        Value::Enum { variant, parts } => {
            // the decode shape mirrored (M4-S45): the kind key holds the
            // variant name (words joined _), the other keys are the
            // variant's parts, written part0.. partN-1 (the read shape
            // key choice is logged in LYKAON_DEVIATIONS.md)
            out.push_str("{\"kind\":");
            json_string_write(&key_of(variant), out);
            for (idx, p) in parts.iter().enumerate() {
                out.push(',');
                json_string_write(&format!("part{idx}"), out);
                out.push(':');
                json_write(p, pretty, depth + 1, out)?;
            }
            out.push('}');
            Ok(())
        }
        Value::Pair(a, b) => {
            out.push('[');
            json_write(a, pretty, depth + 1, out)?;
            out.push(',');
            if pretty {
                out.push(' ');
            }
            json_write(b, pretty, depth + 1, out)?;
            out.push(']');
            Ok(())
        }
        _ => Err(()), // a value json does not hold (Big, files and so on)
    }
}

// =================================================================
// the kind-directed decode (M4-S42..S45)

pub fn decode_fval(f: &FVal, kind: &Kind, depth: usize) -> Result<Value, ()> {
    if depth >= MAX_DEPTH {
        return Err(());
    }
    match kind {
        Kind::Whole => match f {
            FVal::Num(n) => Ok(Value::Whole(as_whole(*n).ok_or(())?)),
            // xml text content and the like arrive as strings; a whole
            // number in word form still reads (logged with the xml cut)
            FVal::Str(s) => Ok(Value::Whole(s.trim().parse::<i64>().map_err(|_| ())?)),
            _ => Err(()),
        },
        Kind::Big => Err(()), // the big kind is no decode target in this cut
        Kind::Decimal => match f {
            FVal::Num(n) => Ok(Value::Dec(*n)),
            FVal::Str(s) => Ok(Value::Dec(s.trim().parse::<f64>().map_err(|_| ())?)),
            _ => Err(()),
        },
        Kind::Text => match f {
            FVal::Str(s) => Ok(Value::Text(s.clone())),
            _ => Err(()),
        },
        // a letter rides on a one-letter text (the value model has no
        // separate letter value)
        Kind::Letter => match f {
            FVal::Str(s) if s.chars().count() == 1 => Ok(Value::Text(s.clone())),
            _ => Err(()),
        },
        Kind::Boolean => match f {
            FVal::Bool(b) => Ok(Value::Boolean(*b)),
            // xml text content reads the two words
            FVal::Str(s) if s.trim() == "true" => Ok(Value::Boolean(true)),
            FVal::Str(s) if s.trim() == "false" => Ok(Value::Boolean(false)),
            _ => Err(()),
        },
        Kind::Maybe(inner) => match f {
            FVal::Null => Ok(Value::Maybe(None)),
            other => Ok(Value::Maybe(Some(Box::new(decode_fval(
                other,
                inner,
                depth + 1,
            )?)))),
        },
        Kind::List(inner) => match f {
            FVal::Arr(items) => {
                let mut out = Vec::new();
                for it in items {
                    out.push(decode_fval(it, inner, depth + 1)?);
                }
                Ok(Value::List(out))
            }
            _ => Err(()),
        },
        Kind::Map(k, v) => match f {
            FVal::Obj(items) => {
                if !matches!(**k, Kind::Text) {
                    return Err(()); // M4-S42: map of text to something
                }
                let mut out: Vec<(Value, Value)> = Vec::new();
                for (key, val) in items {
                    out.push((Value::Text(key.clone()), decode_fval(val, v, depth + 1)?));
                }
                Ok(Value::Map(out))
            }
            _ => Err(()),
        },
        Kind::Record(tname, parts) => {
            let obj = match f {
                FVal::Obj(items) => items,
                _ => return Err(()),
            };
            let mut out: Vec<(String, Value)> = Vec::new();
            for (pn, pk) in parts {
                // the key of a part is its name in lower case with the
                // words joined by _ (M4-S43); the exact name also holds
                let keyed = key_of(pn);
                let exact = pn.to_ascii_lowercase();
                let at = obj.iter().find(|(k, _)| *k == keyed || *k == exact);
                // a maybe part is missing when the key is absent or null
                // (M4-S43); a missing key for a part that is not maybe
                // is a bad format
                let v = match at {
                    Some((_, FVal::Null)) => match pk {
                        Kind::Maybe(_) => Value::Maybe(None),
                        _ => return Err(()),
                    },
                    Some((_, fv)) => decode_fval(fv, pk, depth + 1)?,
                    None => match pk {
                        Kind::Maybe(_) => Value::Maybe(None),
                        _ => return Err(()),
                    },
                };
                out.push((pn.clone(), v));
            }
            Ok(Value::Record(tname.clone(), out))
        }
        Kind::Enum(variants) => {
            // an enum decodes from an object whose key `kind` is the
            // variant name (lower case, words joined _), and whose
            // other keys are the variant's parts (M4-S45). This reader
            // takes {kind: name, partN: value} - logged.
            let obj = match f {
                FVal::Obj(items) => items,
                _ => return Err(()),
            };
            let kindv = obj
                .iter()
                .find(|(k, _)| k == "kind")
                .map(|(_, v)| v)
                .ok_or(())?;
            let variant = match kindv {
                FVal::Str(s) => s.clone(),
                _ => return Err(()),
            };
            let (vname, vparts) = variants
                .iter()
                .find(|(vn, _)| key_of(vn) == variant)
                .ok_or(())?;
            let mut out: Vec<Value> = Vec::new();
            for (idx, (pn, pk)) in vparts.iter().enumerate() {
                // the parts read by their names (S45); a file written by
                // this scheme carries part0.. partN-1 (names are not in
                // the value at encode time), so that spelling holds too
                let keyed = key_of(pn);
                let fallback = format!("part{idx}");
                let at = obj
                    .iter()
                    .find(|(k, _)| *k == keyed)
                    .or_else(|| obj.iter().find(|(k, _)| *k == fallback));
                let fv = at.ok_or(())?;
                out.push(decode_fval(&fv.1, pk, depth + 1)?);
            }
            Ok(Value::Enum {
                variant: vname.clone(),
                parts: out,
            })
        }
        _ => Err(()), // the S42 target kinds only
    }
}

// =================================================================
// TOML

/// The toml subset of M4-S47: tables are records, arrays are lists,
/// inline tables are maps. A decoded record reads from the top-level
/// keys of the document (or from the keys of a single `[table]` header
/// - extra keys are ignored per M4-S43, and both spellings decode). No
/// dates, no multi-line basic scalars; a value that spans lines may
/// only be one array of things.
pub fn parse_toml(s: &str) -> Result<FVal, ()> {
    let mut top: Vec<(String, FVal)> = Vec::new();
    let mut cur_path: Vec<String> = Vec::new();
    let mut lines = s.lines();
    while let Some(line) = lines.next() {
        let t = strip_comment(line).trim();
        if t.is_empty() {
            continue;
        }
        if t.starts_with("[[") {
            if !t.ends_with("]]") {
                return Err(());
            }
            let path = toml_path(t[2..t.len() - 2].trim())?;
            if path.is_empty() {
                return Err(());
            }
            toml_open_array_table(&mut top, &path)?;
            cur_path = path;
            continue;
        }
        if t.starts_with('[') {
            if !t.ends_with(']') {
                return Err(());
            }
            let path = toml_path(t[1..t.len() - 1].trim())?;
            if path.is_empty() {
                return Err(());
            }
            toml_table(&mut top, &path)?;
            cur_path = path;
            continue;
        }
        let eq = find_eq(t)?;
        if eq == 0 {
            return Err(());
        }
        let key = toml_key(t[..eq].trim())?;
        let body = t[eq + 1..].trim();
        if body.is_empty() {
            return Err(());
        }
        if body.starts_with('{') {
            if !(body.ends_with('}') && strings_closed(body)) {
                return Err(());
            }
            let obj = parse_json(body)?;
            toml_put(&mut top, &cur_path, key, obj)?;
            continue;
        }
        if body.starts_with('[') {
            // an array may spill over lines until its ]
            let mut acc = body.to_string();
            while !acc.trim_end().ends_with(']') {
                let more = lines.next().ok_or(())?;
                acc.push(' ');
                acc.push_str(strip_comment(more).trim());
            }
            if !strings_closed(&acc) {
                return Err(());
            }
            let f = parse_json(&acc)?;
            toml_put(&mut top, &cur_path, key, f)?;
            continue;
        }
        if !strings_closed(body) {
            return Err(());
        }
        let f = toml_scalar(body)?;
        toml_put(&mut top, &cur_path, key, f)?;
    }
    Ok(FVal::Obj(top))
}

pub fn toml_decode(s: &str, kind: &Kind) -> Result<Value, ()> {
    let f = parse_toml(s)?;
    decode_fval(&f, kind, 0)
}

fn strip_comment(line: &str) -> &str {
    let mut in_basic = false;
    let mut in_lit = false;
    for (idx, c) in line.char_indices() {
        match c {
            '"' if !in_lit => in_basic = !in_basic,
            '\'' if !in_basic => in_lit = !in_lit,
            '#' if !in_basic && !in_lit => return &line[..idx],
            _ => {}
        }
    }
    line
}

fn find_eq(t: &str) -> Result<usize, ()> {
    let mut in_basic = false;
    let mut in_lit = false;
    for (idx, c) in t.char_indices() {
        match c {
            '"' if !in_lit => in_basic = !in_basic,
            '\'' if !in_basic => in_lit = !in_lit,
            '=' if !in_basic && !in_lit => return Ok(idx),
            _ => {}
        }
    }
    Err(())
}

fn toml_key(t: &str) -> Result<String, ()> {
    if t.is_empty() {
        return Err(());
    }
    if t.starts_with('"') {
        if !(t.len() >= 2 && t.ends_with('"')) {
            return Err(());
        }
        return match parse_json(t)? {
            FVal::Str(s) => Ok(s),
            _ => Err(()),
        };
    }
    if t.starts_with('\'') {
        if !(t.len() >= 2 && t.ends_with('\'')) {
            return Err(());
        }
        return Ok(t[1..t.len() - 1].to_string());
    }
    Ok(t.to_string())
}

/// [a.b.c] -> the path of its keys (quoted parts can carry names with
/// spaces).
fn toml_path(t: &str) -> Result<Vec<String>, ()> {
    let mut parts = Vec::new();
    let mut buf = String::new();
    let mut in_basic = false;
    let mut in_lit = false;
    for c in t.chars() {
        match c {
            '"' if !in_lit => {
                in_basic = !in_basic;
                buf.push('"');
            }
            '\'' if !in_basic => {
                in_lit = !in_lit;
                buf.push('\'');
            }
            '.' if !in_basic && !in_lit => {
                parts.push(toml_key(buf.trim())?);
                buf.clear();
            }
            _ => buf.push(c),
        }
    }
    parts.push(toml_key(buf.trim())?);
    Ok(parts)
}

/// Both string kinds of a fragment are closed (a quick check so a
/// multi-line "..." fails instead of eating the file).
fn strings_closed(t: &str) -> bool {
    let mut in_basic = false;
    let mut in_lit = false;
    for c in t.chars() {
        match c {
            '"' if !in_lit => in_basic = !in_basic,
            '\'' if !in_basic => in_lit = !in_lit,
            _ => {}
        }
    }
    !(in_basic || in_lit)
}

fn toml_slot<'a>(
    top: &'a mut Vec<(String, FVal)>,
    path: &[String],
) -> Result<&'a mut Vec<(String, FVal)>, ()> {
    if path.is_empty() {
        return Ok(top);
    }
    let head = path[0].clone();
    let already = top.iter().position(|(k, _)| *k == head);
    if already.is_none() {
        top.push((head, FVal::Obj(Vec::new())));
    }
    let pos = top.iter().position(|(k, _)| *k == path[0]).ok_or(())?;
    if path.len() == 1 {
        match &mut top[pos].1 {
            FVal::Obj(o) => Ok(o),
            _ => Err(()),
        }
    } else {
        match &mut top[pos].1 {
            FVal::Obj(o) => toml_slot(o, &path[1..]),
            _ => Err(()),
        }
    }
}

fn toml_table(top: &mut Vec<(String, FVal)>, path: &[String]) -> Result<(), ()> {
    toml_slot(top, path)?;
    Ok(())
}

fn toml_open_array_table(top: &mut Vec<(String, FVal)>, path: &[String]) -> Result<(), ()> {
    let (rest, last) = path.split_at(path.len() - 1);
    let slot = toml_slot(top, rest)?;
    let head = last[0].clone();
    let already = slot.iter().position(|(k, _)| *k == head);
    if already.is_none() {
        slot.push((head, FVal::Arr(Vec::new())));
    }
    let pos = slot.iter().position(|(k, _)| *k == last[0]).ok_or(())?;
    match &mut slot[pos] {
        (_, FVal::Arr(a)) => {
            a.push(FVal::Obj(Vec::new()));
            Ok(())
        }
        _ => Err(()),
    }
}

fn toml_put(
    top: &mut Vec<(String, FVal)>,
    path: &[String],
    key: String,
    v: FVal,
) -> Result<(), ()> {
    let slot = toml_slot(top, path)?;
    if slot.iter().any(|(k, _)| *k == key) {
        return Err(()); // a key is defined once per table
    }
    slot.push((key, v));
    Ok(())
}

fn toml_scalar(t: &str) -> Result<FVal, ()> {
    match t {
        "true" => return Ok(FVal::Bool(true)),
        "false" => return Ok(FVal::Bool(false)),
        _ => {}
    }
    if t.starts_with('"') {
        if !(t.len() >= 2 && t.ends_with('"')) {
            return Err(());
        }
        return match parse_json(t)? {
            FVal::Str(s) => Ok(FVal::Str(s)),
            _ => Err(()),
        };
    }
    if t.starts_with('\'') {
        if !(t.len() >= 2 && t.ends_with('\'')) {
            return Err(());
        }
        return Ok(FVal::Str(t[1..t.len() - 1].to_string()));
    }
    let clean: String = t.chars().filter(|c| *c != '_').collect();
    if clean.is_empty() {
        return Err(());
    }
    // a toml number: optional -, digits, optional .digits, optional
    // e±digits (dates and times are not in this subset)
    let b: Vec<char> = clean.chars().collect();
    let mut idx = 0usize;
    let mut saw_digit = false;
    if b.first() == Some(&'-') || b.first() == Some(&'+') {
        idx += 1;
    }
    while idx < b.len() && b[idx].is_ascii_digit() {
        idx += 1;
        saw_digit = true;
    }
    if !saw_digit {
        return Err(());
    }
    if idx < b.len() && b[idx] == '.' {
        idx += 1;
        let mut frac = false;
        while idx < b.len() && b[idx].is_ascii_digit() {
            idx += 1;
            frac = true;
        }
        if !frac {
            return Err(());
        }
    }
    if idx < b.len() && (b[idx] == 'e' || b[idx] == 'E') {
        idx += 1;
        if b.get(idx) == Some(&'+') || b.get(idx) == Some(&'-') {
            idx += 1;
        }
        let mut exp = false;
        while idx < b.len() && b[idx].is_ascii_digit() {
            idx += 1;
            exp = true;
        }
        if !exp {
            return Err(());
        }
    }
    if idx != b.len() {
        return Err(());
    }
    clean.parse::<f64>().map(FVal::Num).map_err(|_| ())
}

/// The toml writer (S46/S47 reversed, logged shape): a record's parts
/// become the table's keys in declaration order; sub-records become
/// [path.to.key] headers; a part holding a list of one record kind
/// becomes [[path.key]] blocks; a part holding a list of scalars becomes
/// a one-line array of those scalars; maps write inline tables; a
/// top-level scalar or a list of scalars writes too (wrapped shapes).
pub fn toml_encode(v: &Value) -> Result<String, ()> {
    let mut out = String::new();
    match v {
        Value::Record(_n, parts) => toml_write_table(parts, &mut Vec::new(), &mut out)?,
        Value::List(items) => {
            let rec = items.iter().collect::<Vec<_>>();
            if !rec.is_empty() && rec.iter().all(|i| matches!(i, Value::Record(..))) {
                let names: Vec<String> = rec
                    .iter()
                    .filter_map(|i| match i {
                        Value::Record(n, _) => Some(key_of(n)),
                        _ => None,
                    })
                    .collect();
                let fname = names.first().ok_or(())?;
                if names.iter().any(|n| n != fname) {
                    return Err(());
                }
                for item in &rec {
                    if let Value::Record(_, parts) = item {
                        out.push_str("[[");
                        out.push_str(fname);
                        out.push_str("]]\n");
                        toml_write_table(parts, &mut Vec::new(), &mut out)?;
                    }
                }
            } else {
                out.push_str("values = [");
                let mut first = true;
                for item in items {
                    if !first {
                        out.push_str(", ");
                    }
                    first = false;
                    toml_scalar_value(item, &mut out)?;
                }
                out.push_str("]\n");
            }
        }
        scalar => {
            toml_scalar_value(scalar, &mut out)?;
            out.push('\n');
        }
    }
    Ok(out)
}

fn toml_write_table(
    parts: &[(String, Value)],
    path: &mut Vec<String>,
    out: &mut String,
) -> Result<(), ()> {
    // the scalar keys of THIS table first (toml shaping), then the keys
    // that hold subtables
    for (pn, pv) in parts {
        let key = strip_trailing_path(pn);
        match pv {
            // a list of scalars wants a one-line array; every other
            // non-scalar holds its own shape in the subtable pass below
            // a list of scalars wants a one-line array; a list of
            // records holds its shape in the subtable pass below; any
            // other list content fails (no toml spelling was used)
            Value::List(items) => {
                let all_scalar = !items.is_empty()
                    && items.iter().all(|i| {
                        matches!(
                            i,
                            Value::Text(_) | Value::Whole(_) | Value::Dec(_) | Value::Boolean(_)
                        )
                    });
                let all_records =
                    !items.is_empty() && items.iter().all(|i| matches!(i, Value::Record(..)));
                if all_scalar {
                    out.push_str(&key);
                    out.push_str(" = [");
                    let mut first = true;
                    for item in items {
                        if !first {
                            out.push_str(", ");
                        }
                        first = false;
                        toml_scalar_value(item, out)?;
                    }
                    out.push_str("]\n");
                } else if !all_records {
                    return Err(());
                }
            }
            Value::Maybe(None) => {
                // a toml table cannot hold a null; the part is absent
            }
            Value::Maybe(Some(inner)) => {
                out.push_str(&key);
                out.push_str(" = ");
                toml_scalar_value(inner, out)?;
                out.push('\n');
            }
            scalar => {
                out.push_str(&key);
                out.push_str(" = ");
                toml_scalar_value(scalar, out)?;
                out.push('\n');
            }
        }
    }
    for (pn, pv) in parts {
        let full = pn.to_string();
        let key = strip_trailing_path(pn);
        let mut this = path.clone();
        this.push(key.clone());
        match pv {
            Value::Record(_, sub) => {
                out.push('[');
                out.push_str(&this.join("."));
                out.push_str("]\n");
                toml_write_table(sub, &mut this, out)?;
            }
            Value::List(items)
                if !items.is_empty() && items.iter().all(|i| matches!(i, Value::Record(..))) =>
            {
                for item in items {
                    if let Value::Record(_, sub) = item {
                        out.push_str("[[");
                        out.push_str(&this.join("."));
                        out.push_str("]]\n");
                        toml_write_table(sub, &mut this.clone(), out)?;
                    }
                }
            }
            _ => {}
        }
        let _ = full;
    }
    Ok(())
}

/// A part name arrives keyed (home_address); a toml key wants just the
/// last word's key (no dots was written, so this is a no-op kept for
/// shape stability).
fn strip_trailing_path(pn: &str) -> String {
    pn.to_string()
}

fn toml_scalar_value(v: &Value, out: &mut String) -> Result<(), ()> {
    match v {
        Value::Text(s) => {
            json_string_write(s, out); // toml basic strings read as json strings
            Ok(())
        }
        Value::Whole(w) => {
            out.push_str(&w.to_string());
            Ok(())
        }
        Value::Dec(d) => {
            out.push_str(&num_text(*d)?);
            Ok(())
        }
        Value::Boolean(b) => {
            out.push_str(if *b { "true" } else { "false" });
            Ok(())
        }
        Value::Maybe(Some(inner)) => toml_scalar_value(inner, out),
        Value::List(items) => {
            out.push('[');
            let mut first = true;
            for i in items {
                if !first {
                    out.push_str(", ");
                }
                first = false;
                toml_scalar_value(i, out)?;
            }
            out.push(']');
            Ok(())
        }
        Value::Map(pairs) => {
            // inline table (M4-S47)
            out.push('{');
            let mut first = true;
            for (k, val) in pairs {
                if !first {
                    out.push_str(", ");
                }
                first = false;
                match k {
                    Value::Text(t) => json_string_write(t, out),
                    _ => return Err(()),
                }
                out.push_str(" = ");
                toml_scalar_value(val, out)?;
            }
            out.push('}');
            Ok(())
        }
        _ => Err(()),
    }
}

// =================================================================
// YAML

/// The block-style subset of the YAML 1.2 core schema (M4-S47): maps
/// and lists block-style, plain and quoted scalars, numbers, true and
/// false and null; anchors, tags and multi-document files fail (which
/// is exactly the doc's bad-format rule).
pub fn parse_yaml(s: &str) -> Result<FVal, ()> {
    let lines: Vec<&str> = s.lines().collect();
    let mut i = 0usize;
    while i < lines.len() && lines[i].trim().is_empty() {
        i += 1;
    }
    if i < lines.len() && (lines[i].trim() == "---" || lines[i].trim() == "...") {
        i += 1; // one document separator before the content is nothing
    }
    for l in &lines[i..] {
        if l.trim() == "---" {
            return Err(()); // a second document
        }
        if l.trim().starts_with('&') || l.trim().contains(" !") || l.trim().starts_with('!') {
            return Err(()); // anchors and tags
        }
    }
    let Some(_) = lines.get(i) else {
        return Ok(FVal::Null);
    };
    let v = yaml_block(&lines, &mut i, 0)?;
    while i < lines.len() && lines[i].trim().is_empty() {
        i += 1;
    }
    if i != lines.len() {
        return Err(()); // content after the first block
    }
    Ok(v)
}

pub fn yaml_decode(s: &str, kind: &Kind) -> Result<Value, ()> {
    let f = parse_yaml(s)?;
    decode_fval(&f, kind, 0)
}

fn yaml_indent(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The first ": " (or a line-final ":") outside quotes.
fn yaml_colon(t: &str) -> Option<usize> {
    let mut in_s = false;
    let mut in_d = false;
    // BYTE indices, because every caller slices `t` at the returned spot
    // (a character index panics inside a multi-byte character - found by
    // the M4 format fuzz).
    let mut it = t.char_indices().peekable();
    while let Some((idx, c)) = it.next() {
        match c {
            '\'' if !in_d => in_s = !in_s,
            '"' if !in_s => in_d = !in_d,
            ':' if !in_s && !in_d => match it.peek() {
                None => return Some(idx),
                Some((_, ' ')) => return Some(idx),
                _ => {}
            },
            _ => {}
        }
    }
    None
}

fn yaml_fval(t: &str) -> Result<FVal, ()> {
    if t.is_empty() {
        return Ok(FVal::Null);
    }
    for bad in ['&', '!', '*'] {
        if t.starts_with(bad) {
            return Err(()); // anchors and tags fail (M4-S47)
        }
    }
    if t.starts_with('"') && t.len() >= 2 {
        if !t.ends_with('"') {
            return Err(());
        }
        return match parse_json(t)? {
            FVal::Str(s) => Ok(FVal::Str(s)),
            _ => Err(()),
        };
    }
    if t.starts_with('\'') && t.len() >= 2 {
        if !t.ends_with('\'') {
            return Err(());
        }
        return Ok(FVal::Str(t[1..t.len() - 1].to_string()));
    }
    match t {
        "true" | "True" | "TRUE" => return Ok(FVal::Bool(true)),
        "false" | "False" | "FALSE" => return Ok(FVal::Bool(false)),
        "null" | "Null" | "NULL" | "~" => return Ok(FVal::Null),
        _ => {}
    }
    // the core schema's plain numbers
    let oknum = t.chars().enumerate().all(|(i, c)| {
        if c.is_ascii_digit() {
            true
        } else if i == 0 && (c == '-' || c == '+') && t.len() > 1 {
            true
        } else if (c == '.' || c == 'e' || c == 'E') && i > 0 && i + 1 < t.len() {
            true
        } else {
            false
        }
    });
    let hasnum = t.chars().any(|c| c.is_ascii_digit());
    if oknum && hasnum {
        let n: f64 = t.parse::<f64>().map_err(|_| ())?;
        return Ok(FVal::Num(n));
    }
    Ok(FVal::Str(t.to_string()))
}

/// Read one yaml block at line `*i`; `min_indent` is the smallest
/// indentation a line of this block may carry.
fn yaml_block(lines: &[&str], i: &mut usize, min_indent: usize) -> Result<FVal, ()> {
    skip_blanks(lines, i);
    if *i >= lines.len() {
        return Ok(FVal::Null);
    }
    let ind = yaml_indent(lines[*i]);
    let t = lines[*i].trim();
    if ind < min_indent {
        return Ok(FVal::Null); // nothing deeper followed; an empty block
    }
    if t.starts_with("- ") || t == "-" {
        return yaml_list(lines, i, ind);
    }
    if yaml_colon(t).is_some() {
        let mut obj: Vec<(String, FVal)> = Vec::new();
        yaml_map_keys(lines, i, ind, &mut obj)?;
        return Ok(FVal::Obj(obj));
    }
    // one plain scalar document (a scalar file)
    let v = yaml_fval(t)?;
    *i += 1;
    Ok(v)
}

fn skip_blanks(lines: &[&str], i: &mut usize) {
    while *i < lines.len() && lines[*i].trim().is_empty() {
        *i += 1;
    }
}

fn yaml_list(lines: &[&str], i: &mut usize, ind: usize) -> Result<FVal, ()> {
    let mut items = Vec::new();
    loop {
        skip_blanks(lines, i);
        if *i >= lines.len() {
            break;
        }
        let l = lines[*i];
        let li = yaml_indent(l);
        if li < ind {
            break;
        }
        if li > ind {
            return Err(()); // a deeper dash belongs to a deeper block
        }
        let t = l.trim();
        if !(t.starts_with("- ") || t == "-") {
            break; // a map's line ends the list
        }
        *i += 1;
        if t == "-" {
            // the item is whatever block follows (deeper or dash)
            let mut j = *i;
            skip_blanks(lines, &mut j);
            if j < lines.len() && yaml_indent(lines[j]) > ind {
                items.push(yaml_block(lines, i, ind + 1)?);
            } else if j < lines.len()
                && yaml_indent(lines[j]) == ind
                && (lines[j].trim().starts_with("- ") || lines[j].trim() == "-")
            {
                items.push(yaml_list(lines, i, ind)?);
            } else {
                items.push(FVal::Null);
            }
            continue;
        }
        let after = &t[2..];
        if let Some(col) = yaml_colon(after) {
            // "- key: value" starts an item map whose logical indent is
            // the dash column + 2 (the logged subset: its later keys
            // sit exactly there)
            let key = yaml_word(after[..col].trim())?;
            let rest = after[col + 1..].trim();
            let first_val = if rest.is_empty() {
                yaml_deeper_or_null(lines, i, ind + 2)?
            } else {
                yaml_fval(rest)?
            };
            let mut obj: Vec<(String, FVal)> = vec![(key, first_val)];
            yaml_map_keys(lines, i, ind + 2, &mut obj)?;
            items.push(FVal::Obj(obj));
        } else {
            items.push(yaml_fval(after)?);
        }
    }
    Ok(FVal::Arr(items))
}

fn yaml_word(t: &str) -> Result<String, ()> {
    match yaml_fval(t)? {
        FVal::Str(s) => Ok(s),
        _ => Ok(t.to_string()),
    }
}

fn yaml_deeper_or_null(lines: &[&str], i: &mut usize, deeper: usize) -> Result<FVal, ()> {
    let mut j = *i;
    skip_blanks(lines, &mut j);
    if j < lines.len() && yaml_indent(lines[j]) >= deeper {
        return yaml_block(lines, i, deeper);
    }
    Ok(FVal::Null)
}

fn yaml_map_keys(
    lines: &[&str],
    i: &mut usize,
    ind: usize,
    obj: &mut Vec<(String, FVal)>,
) -> Result<(), ()> {
    loop {
        skip_blanks(lines, i);
        if *i >= lines.len() {
            break;
        }
        let l = lines[*i];
        let li = yaml_indent(l);
        if li < ind {
            break;
        }
        if li > ind {
            return Err(());
        }
        let t = l.trim();
        if t.starts_with("- ") || t == "-" {
            // a list at the map's own indent fills the still-empty key
            // (the common yaml spelling); with nothing open it is a
            // shape error
            if matches!(obj.last().map(|x| &x.1), Some(FVal::Null)) {
                let v = yaml_list(lines, i, li)?;
                if let Some(slot) = obj.last_mut() {
                    slot.1 = v;
                }
                continue;
            }
            return Err(());
        }
        let Some(col) = yaml_colon(t) else {
            return Err(()); // a map's line carries key: value
        };
        let key = yaml_word(t[..col].trim())?;
        if obj.iter().any(|(k, _)| *k == key) {
            return Err(()); // a key speaks once per map
        }
        let after = t[col + 1..].trim();
        *i += 1;
        if after.is_empty() {
            obj.push((key, yaml_deeper_or_null_or_list(lines, i, ind)?));
        } else {
            obj.push((key, yaml_fval(after)?));
        }
    }
    Ok(())
}

/// After "key:" with nothing on its line: a deeper block, a list at the
/// key's indent, or null (the logged subset has no same-indent map
/// value - a map value sits deeper, as in any block style).
fn yaml_deeper_or_null_or_list(lines: &[&str], i: &mut usize, ind: usize) -> Result<FVal, ()> {
    let mut j = *i;
    skip_blanks(lines, &mut j);
    if j >= lines.len() {
        return Ok(FVal::Null);
    }
    let li = yaml_indent(lines[j]);
    let nt = lines[j].trim();
    if li > ind {
        return yaml_block(lines, i, ind + 1);
    }
    if li == ind && (nt.starts_with("- ") || nt == "-") {
        return yaml_list(lines, i, ind);
    }
    Ok(FVal::Null)
}

/// The yaml writer: block style, two spaces per level, a list under a
/// key writes its dashes at the key's indentation (the same spelling
/// the reader takes).
pub fn yaml_encode(v: &Value) -> Result<String, ()> {
    let mut out = String::new();
    yaml_block_write(v, 0, &mut out, None)?;
    Ok(out)
}

/// One value written in block style at `depth` (indent = depth*2). A
/// scalar is one line; a map or list opens lines below; a record's
/// parts are the map's keys. `key` is the prefix when the caller
/// writes "key: ..." before a nested block (already on the line).
fn yaml_block_write(
    v: &Value,
    depth: usize,
    out: &mut String,
    inline_key: Option<&str>,
) -> Result<(), ()> {
    if depth >= MAX_DEPTH {
        return Err(());
    }
    let pad = "  ".repeat(depth);
    match v {
        Value::Text(s) => {
            out.push_str(&pad);
            if let Some(k) = inline_key {
                out.push_str(&yaml_key_text(k));
                out.push_str(": ");
            }
            out.push_str(&yaml_scalar_text(s));
            out.push('\n');
            Ok(())
        }
        Value::Whole(w) => {
            out.push_str(&pad);
            if let Some(k) = inline_key {
                out.push_str(&yaml_key_text(k));
                out.push_str(": ");
            }
            out.push_str(&w.to_string());
            out.push('\n');
            Ok(())
        }
        Value::Dec(d) => {
            out.push_str(&pad);
            if let Some(k) = inline_key {
                out.push_str(&yaml_key_text(k));
                out.push_str(": ");
            }
            out.push_str(&num_text(*d)?);
            out.push('\n');
            Ok(())
        }
        Value::Boolean(b) => {
            out.push_str(&pad);
            if let Some(k) = inline_key {
                out.push_str(&yaml_key_text(k));
                out.push_str(": ");
            }
            out.push_str(if *b { "true" } else { "false" });
            out.push('\n');
            Ok(())
        }
        Value::Maybe(Some(inner)) => yaml_block_write(inner, depth, out, inline_key),
        Value::Maybe(None) | Value::Missing => {
            out.push_str(&pad);
            if let Some(k) = inline_key {
                out.push_str(&yaml_key_text(k));
                out.push_str(": ");
            }
            out.push_str("null");
            out.push('\n');
            Ok(())
        }
        Value::List(items) => {
            if let Some(k) = inline_key {
                // "key:" then the dashes at the key's indent + 2
                out.push_str(&pad);
                out.push_str(&yaml_key_text(k));
                out.push_str(":\n");
            }
            if items.is_empty() {
                if inline_key.is_none() {
                    out.push_str(&pad);
                    out.push_str("[]\n");
                }
                return Ok(());
            }
            for item in items {
                yaml_dash_item(item, depth + if inline_key.is_some() { 1 } else { 0 }, out)?;
            }
            Ok(())
        }
        Value::Map(pairs) => {
            if let Some(k) = inline_key {
                out.push_str(&pad);
                out.push_str(&yaml_key_text(k));
                out.push_str(":\n");
            }
            for (pk, pv) in pairs {
                let key = match pk {
                    Value::Text(t) => t.clone(),
                    _ => return Err(()), // a yaml map key is text
                };
                yaml_map_value(
                    pv,
                    depth + if inline_key.is_some() { 1 } else { 0 },
                    &key,
                    out,
                )?;
            }
            Ok(())
        }
        Value::Record(_tn, parts) => {
            if let Some(k) = inline_key {
                out.push_str(&pad);
                out.push_str(&yaml_key_text(k));
                out.push_str(":\n");
            }
            for (pn, pv) in parts {
                yaml_map_value(
                    pv,
                    depth + if inline_key.is_some() { 1 } else { 0 },
                    &key_of(pn),
                    out,
                )?;
            }
            Ok(())
        }
        Value::Enum { variant, parts } => {
            // the decode shape mirrored: kind holds the variant, the
            // parts follow part0.. partN-1 (logged)
            let pi: Vec<(String, Value)> = parts
                .iter()
                .enumerate()
                .map(|(idx, p)| (format!("part{idx}"), p.clone()))
                .collect();
            let fake = Value::Record(variant.clone(), pi);
            yaml_block_write(&fake, depth, out, inline_key)
        }
        _ => Err(()),
    }
}

/// "key: value" when the value is a scalar; "key:" + deeper block when
/// it holds a map, a record or a list.
fn yaml_map_value(v: &Value, depth: usize, key: &str, out: &mut String) -> Result<(), ()> {
    if depth >= MAX_DEPTH {
        return Err(());
    }
    // the shape choice is the same either way (a block value writes
    // "key:" plus its block; a scalar writes "key: value" on one line)
    yaml_block_write(v, depth, out, Some(key))
}

fn yaml_dash_item(item: &Value, depth: usize, out: &mut String) -> Result<(), ()> {
    if depth >= MAX_DEPTH {
        return Err(());
    }
    let pad = "  ".repeat(depth);
    // the dash column (a scalar lands on the dash line)
    match item {
        Value::Text(_)
        | Value::Whole(_)
        | Value::Dec(_)
        | Value::Boolean(_)
        | Value::Maybe(None)
        | Value::Maybe(Some(_)) => {
            out.push_str(&pad);
            out.push_str("- ");
            // the scalar's own text without indentation padding
            let mark = out.len();
            yaml_block_write(item, 0, out, None)?;
            let _ = mark;
        }
        Value::List(_) | Value::Map(_) | Value::Record(..) | Value::Enum { .. } => {
            out.push_str("-");
            out.push('\n');
            yaml_block_write(item, depth + 1, out, None)?;
        }
        _ => return Err(()),
    }
    Ok(())
}

fn yaml_key_text(k: &str) -> String {
    yaml_scalar_text(k)
}

fn yaml_scalar_text(s: &str) -> String {
    // a plain scalar when it reads back as a string; json's quoted
    // spelling when the text would read as something else
    let as_f = yaml_fval(s);
    let plain = matches!(as_f, Ok(FVal::Str(_)));
    let special = s.is_empty()
        || s.starts_with(['&', '!', '*', '-'])
        || s.contains(": ")
        || s.ends_with(':')
        || s.starts_with(' ')
        || s.ends_with(' ');
    if plain && !special {
        s.to_string()
    } else {
        let mut q = String::new();
        json_string_write(s, &mut q); // a json string is a yaml 1.2 core string
        q
    }
}

// =================================================================
// XML

/// The xml subset of M4-S47: the element tree. Each element reads to a
/// leaf (content, kept as-is) or to an object of its children when it
/// holds child elements; the root element's name is reported.
pub fn parse_xml(s: &str) -> Result<(String, FVal), ()> {
    let mut p = P::new(s.as_bytes());
    xml_skip_misc(&mut p, true)?;
    let (name, children, content) = xml_element(&mut p, 0)?;
    xml_skip_misc(&mut p, false)?;
    if p.i != p.b.len() {
        return Err(());
    }
    let fval = if children.is_empty() {
        FVal::Str(content)
    } else {
        FVal::Obj(children)
    };
    Ok((name, fval))
}

pub fn xml_decode(text: &str, kind: &Kind) -> Result<Value, ()> {
    let (root_name, f) = parse_xml(text)?;
    // a record decodes from an element named as the kind (words joined
    // by _); the strictness of this check is logged (nothing in the
    // doc says a foreign root name converts)
    let must_name = if let Kind::Record(tn, _) = kind {
        Some(key_of(tn))
    } else {
        None
    };
    if let Some(must) = must_name {
        if root_name != must {
            return Err(());
        }
    }
    let f = xml_leaf_as_empty(f);
    decode_fval(&f, kind, 0)
}

/// An xml element with content holds no null; the "" content of a
/// missing maybe part gives null here (xml cannot spell null - logged).
fn xml_leaf_as_empty(f: FVal) -> FVal {
    match f {
        FVal::Str(s) if s.trim().is_empty() => FVal::Null,
        FVal::Obj(items) => FVal::Obj(
            items
                .into_iter()
                .map(|(k, v)| (k, xml_leaf_as_empty(v)))
                .collect(),
        ),
        FVal::Arr(items) => FVal::Arr(items.into_iter().map(xml_leaf_as_empty).collect()),
        other => other,
    }
}

fn xml_skip_misc(p: &mut P, allow_decl: bool) -> Result<(), ()> {
    loop {
        while p.i < p.b.len() && matches!(p.b[p.i], b' ' | b'\t' | b'\n' | b'\r') {
            p.i += 1;
        }
        if p.i < p.b.len() && p.b[p.i] == b'<' {
            if p.b[p.i..].starts_with(b"<!--") {
                if let Some(rel) = p.b[p.i + 4..].windows(3).position(|w| w == b"-->") {
                    p.i += 4 + rel + 3;
                    continue;
                }
                return Err(());
            }
            if allow_decl && p.b[p.i..].starts_with(b"<?") {
                if let Some(rel) = p.b[p.i + 2..].windows(2).position(|w| w == b"?>") {
                    p.i += 2 + rel + 2;
                    continue;
                }
                return Err(());
            }
            if p.b[p.i..].starts_with(b"<!") {
                if let Some(rel) = p.b[p.i + 2..].iter().position(|c| *c == b'>') {
                    p.i += 2 + rel + 1;
                    continue;
                }
                return Err(());
            }
        }
        return Ok(());
    }
}

/// One element: <name attrs> children-or-content </name>. The children
/// land as Obj(child pairs) (a repeated child name stacks into one
/// Arr), the bare content as Str. Attributes are ignored (M4-S47).
fn xml_element(p: &mut P, depth: usize) -> Result<(String, Vec<(String, FVal)>, String), ()> {
    if depth >= MAX_DEPTH {
        return Err(()); // M4-S48
    }
    if !p.eat(b'<') {
        return Err(());
    }
    // the name: letters, digits and _ - the writer spells words joined
    // by _, and generous readers take them apart again
    let nstart = p.i;
    while p.i < p.b.len()
        && (p.b[p.i].is_ascii_alphanumeric() || p.b[p.i] == b'_' || p.b[p.i] == b'-')
    {
        p.i += 1;
    }
    let name = std::str::from_utf8(&p.b[nstart..p.i])
        .map_err(|_| ())?
        .to_string();
    if name.is_empty() {
        return Err(());
    }
    // attributes and the tag end (/> for self-closed)
    let mut self_closed = false;
    loop {
        if p.i >= p.b.len() {
            return Err(());
        }
        if p.b[p.i] == b'/' && p.b.get(p.i + 1) == Some(&b'>') {
            p.i += 2;
            self_closed = true;
            break;
        }
        if p.b[p.i] == b'>' {
            p.i += 1;
            break;
        }
        if p.b[p.i] == b'"' || p.b[p.i] == b'\'' {
            let q = p.b[p.i];
            p.i += 1;
            while p.i < p.b.len() && p.b[p.i] != q {
                p.i += 1;
            }
            p.i += 1;
            continue;
        }
        p.i += 1;
    }
    let mut children: Vec<(String, FVal)> = Vec::new();
    let mut content = String::new();
    if !self_closed {
        loop {
            // content until the next <; a mix of content and children
            // lets the children rule (logged)
            let mut text = String::new();
            while p.i < p.b.len() && p.b[p.i] != b'<' {
                // one utf-8 letter at a time, unescaping the five
                let rest = std::str::from_utf8(&p.b[p.i..]).map_err(|_| ())?;
                let ch = rest.chars().next().ok_or(())?;
                p.i += ch.len_utf8();
                text.push(ch);
            }
            if !text.is_empty() {
                if content.is_empty() {
                    content.push_str(&xml_text_unescape(&text)?);
                } else {
                    content.push_str(&xml_text_unescape(&text)?);
                }
            }
            if p.i >= p.b.len() {
                return Err(()); // the element never closed
            }
            if p.b[p.i..].starts_with(b"</") {
                // the close tag: it must name this element
                p.i += 2;
                let cstart = p.i;
                while p.i < p.b.len() && p.b[p.i] != b'>' {
                    p.i += 1;
                }
                let cname = std::str::from_utf8(&p.b[cstart..p.i]).map_err(|_| ())?;
                let cname = cname.trim();
                if cname != name {
                    return Err(()); // a mismatched close tag
                }
                p.i += 1;
                break;
            }
            let (cname, cvals, ctext) = xml_element(p, depth + 1)?;
            let cfval = if cvals.is_empty() {
                FVal::Str(ctext)
            } else {
                FVal::Obj(cvals)
            };
            // a list part repeats its element (M4-S47): the same name
            // twice stacks the values into one Arr
            if let Some(slot) = children.iter_mut().find(|(k, _)| *k == cname) {
                if let FVal::Arr(a) = &mut slot.1 {
                    a.push(cfval);
                    continue;
                }
                let old = std::mem::replace(&mut slot.1, FVal::Null);
                slot.1 = FVal::Arr(vec![old, cfval]);
            } else {
                children.push((cname, cfval));
            }
        }
    }
    Ok((name, children, content))
}

fn xml_text_unescape(t: &str) -> Result<String, ()> {
    if !(t.contains('&') && t.contains(';')) {
        return Ok(t.to_string());
    }
    let mut out = String::new();
    let mut rest = t;
    while let Some(amp) = rest.find('&') {
        if rest[..amp].is_empty() {
        } else {
            out.push_str(&rest[..amp]);
        }
        let tail = &rest[amp + 1..];
        let Some(semi) = tail.find(';') else {
            return Err(());
        };
        match &tail[..semi] {
            "lt" => out.push('<'),
            "gt" => out.push('>'),
            "amp" => out.push('&'),
            "apos" => out.push('\''),
            "quot" => out.push('"'),
            c if c.starts_with("#x") || c.starts_with("#X") => {
                let n = u32::from_str_radix(&c[2..], 16).map_err(|_| ())?;
                out.push(char::from_u32(n).ok_or(())?);
            }
            c if c.starts_with('#') => {
                let n: u32 = c[1..].parse().map_err(|_| ())?;
                out.push(char::from_u32(n).ok_or(())?);
            }
            _ => return Err(()),
        }
        rest = &tail[semi + 1..];
    }
    out.push_str(rest);
    Ok(out)
}

/// The xml writer (M4-S47 reversed): an element named as the kind
/// (words joined by _), one child element per part, a text part as
/// content, a list part repeated elements, sub-records nested,
/// attributes never written. An empty maybe part writes an empty
/// element; a repeated part of records nests each.
pub fn xml_encode(v: &Value) -> Result<String, ()> {
    let tname = match v {
        Value::Record(t, _) => key_of(t),
        _ => return Err(()), // the doc's element shape names a kind
    };
    let mut out = String::new();
    xml_write_element(tname, v, &mut out)?;
    Ok(out)
}

fn xml_write_element(name: String, v: &Value, out: &mut String) -> Result<(), ()> {
    xml_write_as(name, v, out)
}

fn xml_write_as(name: String, v: &Value, out: &mut String) -> Result<(), ()> {
    if name.len() > 200 {
        return Err(());
    }
    match v {
        Value::Record(_, parts) => {
            out.push('<');
            out.push_str(&name);
            out.push('>');
            for (pn, pv) in parts {
                xml_write_as(key_of(pn), pv, out)?;
            }
            out.push_str("</");
            out.push_str(&name);
            out.push('>');
            Ok(())
        }
        Value::List(items) | Value::Set(items) | Value::Queue(items) => {
            // a list part repeats its element (M4-S47)
            for item in items {
                xml_write_as(name.clone(), item, out)?;
            }
            Ok(())
        }
        Value::Enum { variant, parts } => {
            // no enum spelling is given by the doc for xml (the decode
            // refuses one - logged), so an xml write of one fails too
            let _ = (variant, parts);
            Err(())
        }
        Value::Map(_) => {
            // no map spelling either: a map in xml fails (logged)
            Err(())
        }
        Value::Maybe(Some(inner)) => xml_write_as(name, inner, out),
        Value::Maybe(None) => {
            out.push('<');
            out.push_str(&name);
            out.push_str("></");
            out.push_str(&name);
            out.push('>');
            Ok(())
        }
        Value::Text(s) => {
            out.push('<');
            out.push_str(&name);
            out.push('>');
            out.push_str(&xml_text_escape(s));
            out.push_str("</");
            out.push_str(&name);
            out.push('>');
            Ok(())
        }
        Value::Whole(w) => {
            let fake = Value::Text(w.to_string());
            xml_write_as(name, &fake, out)
        }
        Value::Dec(d) => {
            let fake = Value::Text(num_text(*d)?);
            xml_write_as(name, &fake, out)
        }
        Value::Boolean(b) => {
            let fake = Value::Text(if *b {
                "true".to_string()
            } else {
                "false".to_string()
            });
            xml_write_as(name, &fake, out)
        }
        _ => Err(()),
    }
}

fn xml_text_escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '\'' => out.push_str("&apos;"),
            '"' => out.push_str("&quot;"),
            c => out.push(c),
        }
    }
    out
}

// =================================================================
// CSV (M4-S47 + RFC 4180: quotes, doubled quotes and line breaks
// inside quoted cells are read)

/// The rows of a csv file (the header included as row 0).
pub fn parse_csv(s: &str) -> Result<Vec<Vec<String>>, ()> {
    let mut rows: Vec<Vec<String>> = Vec::new();
    let mut cell = String::new();
    let mut row: Vec<String> = Vec::new();
    let mut in_quotes = false;
    let mut b = s.chars().peekable();
    while let Some(c) = b.next() {
        if in_quotes {
            match c {
                '"' => {
                    if b.peek() == Some(&'"') {
                        cell.push('"');
                        b.next();
                    } else {
                        in_quotes = false;
                    }
                }
                c => cell.push(c),
            }
            continue;
        }
        match c {
            '"' => in_quotes = true,
            ',' => {
                row.push(std::mem::take(&mut cell));
            }
            '\r' => {
                if b.peek() == Some(&'\n') {
                    b.next();
                }
                row.push(std::mem::take(&mut cell));
                rows.push(std::mem::take(&mut row));
            }
            '\n' => {
                row.push(std::mem::take(&mut cell));
                rows.push(std::mem::take(&mut row));
            }
            c => cell.push(c),
        }
    }
    if in_quotes {
        return Err(()); // a quote ran off the file
    }
    if !(cell.is_empty() && row.is_empty()) {
        row.push(cell);
        rows.push(row);
    }
    Ok(rows)
}

/// A csv decode: the header row names the parts (as for json keys,
/// M4-S43), and every following row is one T (M4-S47). A target of
/// map/list-of-scalar/whatever fails here (the compile check names
/// list-of-record; logged).
pub fn csv_decode(text: &str, kind: &Kind) -> Result<Value, ()> {
    let rows = parse_csv(text)?;
    let Kind::List(inner) = kind else {
        return Err(());
    };
    let Kind::Record(_tn, parts) = &**inner else {
        return Err(());
    };
    let Some(header) = rows.iter().find(|_| true) else {
        return Err(()); // an empty file has no header
    };
    // the header names give the part positions (keyed; the exact
    // spelling also holds, M4-S43)
    let mut col_of_part: Vec<Option<usize>> = vec![None; parts.len()];
    for (idx, h) in header.iter().enumerate() {
        let keyed = key_of(h);
        let exact = h.to_ascii_lowercase();
        if let Some(pi) = parts
            .iter()
            .position(|(pn, _)| key_of(pn) == keyed || pn.to_ascii_lowercase() == exact)
        {
            col_of_part[pi] = Some(idx);
        }
    }
    if col_of_part.iter().any(Option::is_none) {
        return Err(()); // a header name no part carries
    }
    let mut out = Vec::new();
    for row in rows.iter().skip(1) {
        let mut vals: Vec<(String, Value)> = Vec::new();
        for (part_idx, (pn, pk)) in parts.iter().enumerate() {
            let missing = matches!(pk, Kind::Maybe(_));
            let cell = col_of_part[part_idx].and_then(|ci| row.get(ci));
            let v = match cell {
                Some(c) if c.is_empty() && missing => Value::Maybe(None),
                Some(c) => csv_cell(c, pk)?,
                None => {
                    if missing {
                        Value::Maybe(None)
                    } else {
                        return Err(()); // a row missing a plain part's cell
                    }
                }
            };
            vals.push((pn.clone(), v));
        }
        out.push(Value::Record(_tn.clone(), vals));
    }
    Ok(Value::List(out))
}

/// One csv cell coerced by the part kind (the cell is text; the cell
/// text for a number kind must read as that kind - logged).
fn csv_cell(cell: &str, pk: &Kind) -> Result<Value, ()> {
    match pk {
        Kind::Whole => {
            let n: f64 = cell.parse::<f64>().map_err(|_| ())?;
            Ok(Value::Whole(as_whole(n).ok_or(())?))
        }
        Kind::Decimal => Ok(Value::Dec(cell.parse::<f64>().map_err(|_| ())?)),
        Kind::Text => Ok(Value::Text(cell.to_string())),
        // a letter cell is one letter (the value model has no letter value)
        Kind::Letter => {
            if cell.chars().count() == 1 {
                Ok(Value::Text(cell.to_string()))
            } else {
                Err(())
            }
        }
        Kind::Boolean => match cell {
            "true" => Ok(Value::Boolean(true)),
            "false" => Ok(Value::Boolean(false)),
            _ => Err(()),
        },
        Kind::Maybe(inner) => {
            if cell.is_empty() {
                Ok(Value::Maybe(None))
            } else {
                Ok(Value::Maybe(Some(Box::new(csv_cell(cell, inner)?))))
            }
        }
        _ => Err(()),
    }
}

/// The csv writer (M4-S47 reversed): a list of one record kind writes
/// the header row from the parts' names, then a row per record; a cell
/// holds RFC 4180 quotes only when it needs them.
pub fn csv_encode(v: &Value) -> Result<String, ()> {
    let items = match v {
        Value::List(items) => items,
        _ => return Err(()),
    };
    let Some(first) = items.first() else {
        return Ok(String::new()); // an empty list with no header shape
    };
    let Value::Record(tn, parts) = first else {
        return Err(());
    };
    let mut out = String::new();
    let header: Vec<String> = parts.iter().map(|(pn, _)| key_of(pn)).collect();
    out.push_str(&csv_row(&header));
    out.push_str("\r\n");
    for item in items {
        match item {
            Value::Record(rn, vals) => {
                if key_of(rn) != key_of(tn) {
                    return Err(()); // one kind per csv file
                }
                let mut cells = Vec::new();
                for (_, pv) in vals {
                    cells.push(csv_cell_text(pv)?);
                }
                out.push_str(&csv_row(&cells));
                out.push_str("\r\n");
            }
            _ => return Err(()),
        }
    }
    Ok(out)
}

fn csv_row(cells: &[String]) -> String {
    cells.join(",")
}

fn csv_cell_text(v: &Value) -> Result<String, ()> {
    match v {
        Value::Maybe(None) => Ok(String::new()),
        Value::Maybe(Some(inner)) => csv_cell_text(inner),
        Value::Missing => Ok(String::new()),
        Value::Whole(w) => Ok(w.to_string()),
        Value::Dec(d) => num_text(*d),
        Value::Boolean(b) => Ok(if *b {
            "true".to_string()
        } else {
            "false".to_string()
        }),
        Value::Text(s) => {
            if s.contains(',') || s.contains('"') || s.contains('\n') || s.contains('\r') {
                Ok(format!("\"{}\"", s.replace('"', "\"\"")))
            } else {
                Ok(s.to_string())
            }
        }
        _ => Err(()),
    }
}

// =================================================================
// the one decode entry the interpreter calls

pub fn decode_format(format: &str, text: &str, kind: &Kind) -> Result<Value, ()> {
    match format {
        "json" => json_decode(text, kind),
        "toml" => toml_decode(text, kind),
        "yaml" => yaml_decode(text, kind),
        "xml" => xml_decode(text, kind),
        "csv" => csv_decode(text, kind),
        _ => Err(()),
    }
}

pub fn encode_format(format: &str, v: &Value, pretty: bool) -> Result<String, ()> {
    match format {
        "json" => {
            if pretty {
                json_pretty(v)
            } else {
                json_compact(v)
            }
        }
        "toml" => toml_encode(v),
        "yaml" => yaml_encode(v),
        "xml" => xml_encode(v),
        "csv" => csv_encode(v),
        _ => Err(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression (M4 format fuzz): the YAML key colon was reported as a
    /// CHARACTER index but used as a BYTE index, panicking inside a
    /// multi-byte character.
    #[test]
    fn yaml_colon_handles_multibyte_text() {
        let _ = parse_yaml("😀: 1\n");
        let _ = parse_yaml("a😀: b\n");
        let _ = parse_yaml("name: 😀\n");
        let _ = parse_yaml("\"😀\": 1\n");
        let v = parse_yaml("name: Maya\nage: 3\n").expect("a map");
        assert!(matches!(v, FVal::Obj(_)));
        // the returned index must slice cleanly
        let t = "😀: x";
        let c = yaml_colon(t).expect("a colon");
        assert_eq!(&t[..c], "😀");
        assert_eq!(&t[c + 1..], " x");
    }
}
