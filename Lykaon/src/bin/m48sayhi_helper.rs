//! Test helper for the M4-8 `Run` cases (tests/m4.rs): prints
//! `helper <args>` so a Lykaon program can observe a child program's
//! standard output and its one-argument-per-operand invocation.
//!
//! It is a real cargo binary (like the fuzz bins) instead of a raw
//! `rustc` link from the test: the rustc link searched the stale
//! artifacts in target/debug/deps and failed with E0460 once two
//! lykaon_core builds were newer than the lykaon rlib.

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    println!("helper {}", args.join(" "));
}
