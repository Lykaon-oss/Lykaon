//! M4 fuzz (Appendix K M4-T34): feed pseudo-random and structured input into
//! the lexer, parser and checker (through check_source/format_source/
//! run_source_budgeted/test_source), the JSON, TOML, YAML, XML and CSV
//! parsers and decoders, and the HTTP request parser. The compiler must never
//! panic; the step budget stops runaway programs instead of hanging.
//!
//! Run: cargo run --release --bin m4_fuzz -- 600
//! (the milestone requires ten minutes: 600 seconds)

use lykaon::{check_source, format_source, run_source_budgeted, test_source};
use lykaon_core::formats;
use lykaon_core::net;
use lykaon_core::sem::Kind;

use std::time::{Duration, Instant};

/// XORSHIFT: deterministic pseudo-random bytes, same seeds on Windows and Linux.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

/// Words from M1-M4: grammar, names, kinds, the M4 sentence vocabulary.
const POOL: &[&str] = &[
    "Say",
    "If",
    "Otherwise",
    "Repeat",
    "forever",
    "while",
    "For",
    "each",
    "from",
    "in",
    "Note",
    "About",
    "Changeable",
    "Constant",
    "Set",
    "to",
    "Ask",
    "as",
    "number",
    "Stop",
    "Skip",
    "that",
    "literally",
    "lines",
    "give",
    "back",
    "Combine",
    "with",
    "Apply",
    "defaulting",
    "plus",
    "minus",
    "times",
    "divided",
    "by",
    "rounded",
    "at",
    "least",
    "most",
    "and",
    "or",
    "not",
    "is",
    "close",
    "between",
    "list",
    "of",
    "pair",
    "first",
    "second",
    "sorted",
    "joined",
    "space",
    "it",
    "them",
    "this",
    "hello",
    "world",
    "price",
    "count",
    "age",
    "x",
    "y",
    "n",
    "double",
    "lend",
    "change",
    "failing",
    "missing",
    "yes",
    "no",
    "map",
    "set",
    "queue",
    "union",
    "overlap",
    "difference",
    "Put",
    "Add",
    "Remove",
    "empty",
    "has",
    "value",
    "under",
    "unique",
    "reversed",
    "trimmed",
    "upper",
    "lower",
    "split",
    "replace",
    "position",
    "digits",
    "letters",
    "optional",
    "anything",
    "starts",
    "ends",
    "normalized",
    "Try",
    "Fail",
    "Pass",
    "fallback",
    "can",
    "fail",
    "copy",
    "share",
    "weak",
    "Move",
    "Look",
    "When",
    "A",
    "person",
    "record",
    "Test",
    "Check",
    "Pretend",
    "Use",
    "Share",
    "Requires",
    "Ensures",
    "checked",
    "Always",
    "Hand",
    "Tagged",
    // M4
    "Start",
    "task",
    "Wait",
    "Do",
    "these",
    "together",
    "Sleep",
    "Send",
    "Receive",
    "channel",
    "guarded",
    "atomic",
    "counter",
    "After",
    "Every",
    "workers",
    "Spread",
    "Read",
    "Write",
    "Append",
    "file",
    "folder",
    "temporary",
    "named",
    "exists",
    "Fetch",
    "Post",
    "Serve",
    "port",
    "Respond",
    "status",
    "json",
    "template",
    "Page",
    "request",
    "session",
    "Log",
    "info",
    "warning",
    "error",
    "level",
    "settings",
    "Run",
    "Exit",
    "Environment",
    "Takes",
    "Option",
    "random",
    "hash",
    "secret",
    "reveal",
    "date",
    "today",
    "moment",
    "duration",
    "seed",
    "zip",
    "gzip",
    "list",
    "files",
    "Needs",
    "git",
    "version",
    "Live",
    "connection",
    "opens",
    "arrive",
    "20",
    "0",
    "-5",
    "2.5",
    "0.1",
    "99999999999999999999",
    "2026",
    ".",
    "?",
    "!",
    "\"",
    "'",
    ",",
    ":",
    "(",
    ")",
    "$",
    "%",
    "#",
    "/",
    "\\",
    "&",
    "=",
    "é",
    "——",
    "✓",
    "\t",
    "    ",
    "  ",
    "\n",
    "",
    "\0",
    "\u{1F600}",
];

fn make_source(rng: &mut Rng) -> String {
    let mut s = String::new();
    let lines = 1 + rng.below(8);
    for _ in 0..lines {
        let indent = match rng.below(5) {
            0 | 4 => "",
            1 => "    ",
            2 => "  ",
            3 => "        ",
            _ => "",
        };
        s.push_str(indent);
        if rng.below(2) == 0 {
            let words = 1 + rng.below(10);
            for _ in 0..words {
                s.push_str(rng.pick(POOL));
                s.push(' ');
            }
        } else {
            let shape = rng.below(18);
            match shape {
                0 => s.push_str("Say hello.\n"),
                1 => s.push_str("x is 1 plus 2.\n"),
                2 => s.push_str("Start task t.\n    Give back 1.\nWait for t.\n"),
                3 => s.push_str(
                    "Bag is channel of whole number.\nSend 1 to bag.\nReceive from bag.\n",
                ),
                4 => s.push_str("Tally is guarded 0.\nSet tally to tally plus 1.\n"),
                5 => {
                    let f = rng.below(7);
                    let f = ["json", "toml", "yaml", "xml", "csv"][f as usize % 5];
                    s.push_str(&format!(
                        "A rock has weight as whole number.\nSave a rock with weight 1 as {f} to file m4fz in temporary folder.\n"
                    ));
                }
                6 => s.push_str("Fetch plain nowhere dot invalid home.\n"),
                7 => s.push_str(
                    "Serve on port 0.\n    When someone gets home.\n        Respond with hi.\n",
                ),
                8 => s.push_str("Use seed 42.\nSay random number from 1 to 9.\n"),
                9 => s.push_str("Log info hello.\nUse log level debug.\n"),
                10 => s.push_str("If 1 is 1.\n    Say yes.\nOtherwise.\n    Say no.\n"),
                11 => s.push_str("Repeat 2 times.\n    Say tick.\n"),
                12 => s.push_str("d is date 2026 and 2 and 30.\n"),
                13 => s.push_str("Say hash of hello.\n"),
                14 => s.push_str("Page users page is users.\n"),
                15 => s.push_str("Read file m4fz in temporary folder.\n"),
                16 => s.push_str("Run m4fz.\n"),
                _ => {
                    let n = rng.below(8);
                    for _ in 0..n {
                        s.push_str(rng.pick(POOL));
                        s.push(' ');
                    }
                    s.push('\n');
                }
            }
        }
    }
    s
}

/// Text fragments for the format parsers: pieces of real documents plus
/// random junk.
const FORMAT_POOL: &[&str] = &[
    "{",
    "}",
    "[",
    "]",
    "\"",
    "\"key\"",
    "\"value\"",
    ":",
    ",",
    "null",
    "true",
    "false",
    "0",
    "-1",
    "1.5",
    "1e9",
    "\n",
    " ",
    "\t",
    "name",
    "age",
    "kind",
    "<a>",
    "</a>",
    "<root>",
    "</root>",
    "a = 1",
    "[table]",
    "key = ",
    "\"unterminated",
    "\\uD800",
    "---",
    "- item",
    "key: value",
    "a,b,c",
    "\"a\",\"b\"",
    "1,2,3",
    "&amp;",
    "<!-- c -->",
    "<?xml version=\"1.0\"?>",
    "[[array]]",
    "nested: {a: 1}",
    "\u{1F600}",
    "\0",
    "#",
];

fn make_document(rng: &mut Rng) -> String {
    let n = 1 + rng.below(40);
    let mut s = String::new();
    for _ in 0..n {
        s.push_str(rng.pick(FORMAT_POOL));
    }
    s
}

fn fuzz_formats(rng: &mut Rng) {
    let doc = make_document(rng);
    let _ = formats::parse_json(&doc);
    let _ = formats::parse_toml(&doc);
    let _ = formats::parse_yaml(&doc);
    let _ = formats::parse_xml(&doc);
    let _ = formats::parse_csv(&doc);
    // the typed decoders (the depth limit and the kind-directed walk)
    let kinds = [
        Kind::Text,
        Kind::Whole,
        Kind::List(Box::new(Kind::Whole)),
        Kind::Map(Box::new(Kind::Text), Box::new(Kind::Text)),
        Kind::Record(
            "rock".to_string(),
            vec![("weight".to_string(), Kind::Whole)],
        ),
    ];
    let kind = rng.pick(&kinds);
    let _ = formats::decode_format("json", &doc, kind);
    let _ = formats::decode_format("toml", &doc, kind);
    let _ = formats::decode_format("yaml", &doc, kind);
    let _ = formats::decode_format("xml", &doc, kind);
    let _ = formats::decode_format("csv", &doc, kind);
    // encoders over the decoded value keep the round trip honest
    if let Ok(v) = formats::decode_format("json", &doc, kind) {
        let _ = formats::json_compact(&v);
        let _ = formats::json_pretty(&v);
        let _ = formats::toml_encode(&v);
        let _ = formats::yaml_encode(&v);
        let _ = formats::xml_encode(&v);
        let _ = formats::csv_encode(&v);
    }
}

fn fuzz_http(rng: &mut Rng) {
    // random bytes as the socket read: finite chunks, then 0 (closed)
    let n = rng.below(400) as usize;
    let mut bytes = Vec::with_capacity(n);
    for _ in 0..n {
        bytes.push(rng.below(256) as u8);
    }
    // sometimes start with a real-looking request line
    if rng.below(2) == 0 {
        let verb = rng.pick(&["GET", "POST", "PUT", "DELETE", "PATCH", "BOGUS"]);
        let path = rng.pick(&["/", "/users/42", "/a?b=c", "/%zz", "//", "/a/../b"]);
        let version = rng.pick(&["HTTP/1.1", "HTTP/1.0", "HTTP/9.9", ""]);
        let mut head = format!("{verb} {path} {version}\r\n");
        let extras = rng.below(4);
        for _ in 0..extras {
            let k = rng.pick(&[
                "Host",
                "Content-Length",
                "Connection",
                "X-",
                "",
                "Content-Length",
            ]);
            let v = rng.pick(&[
                "127.0.0.1",
                "0",
                "999999999999",
                "keep-alive",
                "close",
                "-1",
            ]);
            head.push_str(&format!("{k}: {v}\r\n"));
        }
        head.push_str("\r\n");
        bytes = head.into_bytes();
        let body = rng.below(50) as usize;
        for _ in 0..body {
            bytes.push(rng.below(256) as u8);
        }
    }
    let mut cursor = 0usize;
    let chunk = 1 + rng.below(64) as usize;
    let mut carry: Vec<u8> = Vec::new();
    let mut read = |buf: &mut [u8]| -> Result<usize, net::NetFail> {
        if cursor >= bytes.len() {
            return Ok(0);
        }
        let take = chunk.min(buf.len()).min(bytes.len() - cursor);
        buf[..take].copy_from_slice(&bytes[cursor..cursor + take]);
        cursor += take;
        Ok(take)
    };
    let _ = net::read_server_request_buffered(&mut carry, &mut read);
    // percent/url decoding on the same input
    let as_text = String::from_utf8_lossy(&bytes).to_string();
    let _ = net::url_decode(&as_text);
    // the WebSocket frame reader on the same bytes
    let mut wcur = 0usize;
    let wbytes = bytes.clone();
    let mut wread = |buf: &mut [u8]| -> Result<usize, net::NetFail> {
        if wcur >= wbytes.len() {
            return Ok(0);
        }
        let take = buf.len().min(wbytes.len() - wcur);
        buf[..take].copy_from_slice(&wbytes[wcur..wcur + take]);
        wcur += take;
        Ok(take)
    };
    let _ = net::ws_read_frame(&mut wread);
}

fn main() {
    let seconds: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(600);
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let started = Instant::now();
    let deadline = Duration::from_secs(seconds);
    let mut runs = 0u64;
    let mut source_runs = 0u64;
    let mut format_runs = 0u64;
    let mut http_runs = 0u64;
    while started.elapsed() < deadline {
        for _ in 0..20 {
            let src = make_source(&mut rng);
            let _ = check_source(&src, "fuzz.lykaon");
            let _ = format_source(&src);
            let _ = run_source_budgeted(&src, "fuzz.lykaon", "", 100_000);
            let _ = test_source(&src, "fuzz.lykaon", "");
            source_runs += 1;
            fuzz_formats(&mut rng);
            format_runs += 1;
            fuzz_http(&mut rng);
            http_runs += 1;
            runs += 1;
        }
        if runs % 2000 < 20 {
            eprintln!(
                "m4_fuzz: {runs} rounds ({source_runs} source, {format_runs} format, {http_runs} http) in {:?}",
                started.elapsed()
            );
        }
    }
    println!(
        "m4_fuzz: clean, {runs} rounds in {:?} (source {source_runs}, formats {format_runs}, HTTP {http_runs})",
        started.elapsed()
    );
}
