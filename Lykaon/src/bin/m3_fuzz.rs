//! M3 fuzz: feed pseudo-random (and structured) sources into check_source,
//! format_source, run_source_budgeted and test_source.
//! The program must never panic (the step budget stops infinite loops instead
//! of hanging). Run: cargo run --release --bin m3_fuzz -- 600
use lykaon::{check_source, format_source, run_source_budgeted, test_source};

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

/// Words from M2 plus M3 additions: interfaces, generators, closures, contracts, tags.
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
    "Test",
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
    "",
    // M3 additions
    "Anything",
    "that",
    "must",
    "can",
    "speak",
    "fly",
    "speak",
    "as",
    "any",
    "speaker",
    "comparer",
    "By",
    "default",
    "says",
    "nothing",
    "Tagged",
    "test",
    "deprecated",
    "slow",
    "Requires",
    "Ensures",
    "checked",
    "Always",
    "Hand",
    "back",
    "HandBack",
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
        let strategy = rng.below(2);
        if strategy == 0 {
            let words = 1 + rng.below(10);
            for _ in 0..words {
                s.push_str(POOL[rng.below(POOL.len() as u64) as usize]);
                s.push(' ');
            }
        } else {
            let shape = rng.below(25);
            match shape {
                0 => s.push_str("Say hello."),
                1 => s.push_str("Numbers is list of 5 and 2 and 8. Say numbers sorted."),
                2 => s.push_str("Changeable ages is map of text to number. Put 31 in ages under Maya."),
                3 => s.push_str("Changeable tags is set of text. Put red in tags."),
                4 => s.push_str("Phone is missing as maybe number. Say phone fallback 0."),
                5 => s.push_str("A person has name as text and age as number. Maya is a person with name Maya and age 31."),
                6 => s.push_str("A color is red or green or blue. Look at shade."),
                7 => s.push_str("To halve n can fail. Try halve 0. If that fails. Say no."),
                8 => s.push_str("To pad lend to change items. Add 0 to items. Give back how many in items."),
                9 => s.push_str("Changeable numbers is list of 5 and 2. Give numbers to pad."),
                10 => s.push_str("Line is cat sat down. Say line joined with space."),
                11 => s.push_str("Say replace one or more digits with x in phrase."),
                12 => s.push_str("Test double works. Check that double 21 is 42."),
                13 => s.push_str("Test halving zero fails. Check that this fails. Say halve 0."),
                14 => s.push_str("Test the bonus. Pretend now gives 5. Check that now is 5."),
                15 => s.push_str("Check for any number n. Check that n plus 0 is n."),
                16 => s.push_str("Use helper. Say double 21."),
                17 => s.push_str("Share double. To double n give n times 2."),
                18 => s.push_str("For each name and age in ages. Say name age."),
                19 => s.push_str("Spot is pair of 1 and 2. Say first of spot."),
                // M3 additions
                20 => s.push_str("Anything that can speak must have speak."),
                21 => s.push_str("A dog can speak."),
                22 => s.push_str("Rex is a dog with name Rex. Say speak Rex."),
                23 => s.push_str("Rex is a dog with name Rex. Say speak Rex as any speaker."),
                24 => s.push_str("To loud pet as anything that can speak Give back speak pet. Say loud Rex."),
                25 => s.push_str("By default speak says nothing."),
                26 => s.push_str("Tagged test. To tagged_func x give back x times 2."),
                27 => s.push_str("Say tagged_func 5."),
                28 => s.push_str("To factorial n give back n."),
                29 => s.push_str("Say factorial 5."),
                30 => s.push_str("Say primes to 50."),
                _ => s.push_str("Say hello."),
            }
        }
        match rng.below(6) {
            0 => s.push_str("  "),
            1 => s.push_str("\t"),
            _ => {}
        }
        s.push('\n');
        if rng.below(8) == 0 {
            s.push('\n');
        }
    }
    s
}

fn main() {
    let secs: u64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(600);
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
        if let Ok(formatted) = &b {
            let formatted = formatted.clone();
            let c = std::panic::catch_unwind(move || check_source(&formatted, "input.lykaon"));
            if c.is_err() {
                eprintln!("PANIC (format->check) on input:\n{:?}\n", src);
                std::process::exit(1);
            }
        }
        let srcr = src.clone();
        let d = std::panic::catch_unwind(move || {
            run_source_budgeted(&srcr, "input.lykaon", "Maya\n", 100_000)
        });
        let srct = src.clone();
        let e = std::panic::catch_unwind(move || test_source(&srct, "input.lykaon", "Maya\n"));
        if a.is_err() || b.is_err() || d.is_err() || e.is_err() {
            eprintln!("PANIC on input:\n{:?}\n", src);
            std::process::exit(1);
        }
        runs += 1;
    }
    println!("fuzz done: {} runs in {}s, no panic", runs, secs);
}
