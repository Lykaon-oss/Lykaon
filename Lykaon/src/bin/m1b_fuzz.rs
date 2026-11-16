//! M1b fuzz: feed pseudo-random (and structured) sources into check_source,
//! format_source and a budgeted run for a fixed duration. The program must
//! never panic (the step budget stops infinite loops instead of hanging).
//! Run: cargo run --release --bin m1b_fuzz -- 600
use lykaon::{check_source, format_source, run_source_budgeted};

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
}

/// Words drawn from every part of the book's M1b surface: m1a words plus
/// lists, loops, functions, pronouns, pairs, kind words and unicode junk.
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
    "factorial",
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
    "pad",
    "lend",
    "change",
    "failing",
    "missing",
    "yes",
    "no",
    "20",
    "0",
    "-5",
    "2.5",
    "0.1",
    "99999999999999999999",
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
    "é",
    "——",
    "✓",
    "\t",
    "    ",
    "  ",
    "\n",
    "", /* empty string exercises token boundaries */
];

fn make_source(rng: &mut Rng) -> String {
    // Two strategies: fully random byte soup from the pool, and
    // structured lines with realistic shapes.
    let strategy = rng.below(2);
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
        if strategy == 0 {
            let words = 1 + rng.below(10);
            for _ in 0..words {
                s.push_str(POOL[rng.below(POOL.len() as u64) as usize]);
                s.push(' ');
            }
        } else {
            // Structured shapes near real M1b sentences.
            let shape = rng.below(14);
            match shape {
                0 => s.push_str("Say hello."),
                1 => s.push_str("Price is 20. Tax is 5. Say price plus tax."),
                2 => s.push_str("Changeable count is 0. Set count to count plus 1."),
                3 => s.push_str("If age is at least 18."),
                4 => s.push_str("Repeat 3 times say hi."),
                5 => s.push_str("Repeat while count is at most 3."),
                6 => s.push_str("Numbers is list of 5 and 2 and 8. Combine numbers with plus."),
                7 => s.push_str("To double n give n times 2. Apply double to each of numbers."),
                8 => s.push_str("For each n from 1 to 5. Say n."),
                9 => s.push_str("Total is pair of 1 and 2. Say first of total."),
                10 => s.push_str("Left order is left sorted. Say if left is right."),
                11 => s.push_str("Say it. Say them. Say that."),
                12 => s.push_str("To greet person with greeting defaulting to hello. Give back pieces joined with space."),
                _ => s.push_str("Spot is missing. Answer is 2 plus 3 times 4."),
            }
        }
        // Random trailing whitespace / period issues.
        match rng.below(6) {
            0 => s.push_str("  "),
            1 => s.push_str("\t"),
            _ => {}
        }
        s.push('\n');
        if rng.below(8) == 0 {
            s.push('\n'); // blank lines, to exercise the two-in-a-row check
        }
    }
    s
}

fn main() {
    let secs: u64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(600);
    // Silence panics inside the fuzz loop; a panic is still a failure (catch_unwind).
    std::panic::set_hook(Box::new(|_| {}));
    let start = Instant::now();
    let budget = Duration::from_secs(secs);
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let mut runs: u64 = 0;
    while start.elapsed() < budget {
        let src = make_source(&mut rng);
        let src_copy = src.clone();
        let a = std::panic::catch_unwind(move || check_source(&src_copy, "input.lykaon"));
        let scr = src.clone();
        let b = std::panic::catch_unwind(move || format_source(&scr));
        // Feeding the formatter's own output back must also be safe.
        if let Ok(formatted) = &b {
            let formatted = formatted.clone();
            let c = std::panic::catch_unwind(move || check_source(&formatted, "input.lykaon"));
            if c.is_err() {
                eprintln!("PANIC (format->check) on input:\n{:?}\n", src);
                std::process::exit(1);
            }
        }
        // M1b adds the interpreter: run with a step budget so runaway loops
        // end with a fixed message instead of a hang.
        let srcr = src.clone();
        let d = std::panic::catch_unwind(move || {
            run_source_budgeted(&srcr, "input.lykaon", "Maya\n", 100_000)
        });
        if a.is_err() || b.is_err() || d.is_err() {
            eprintln!("PANIC on input:\n{:?}\n", src);
            std::process::exit(1);
        }
        runs += 1;
    }
    println!("fuzz done: {} runs in {}s, no panic", runs, secs);
}
