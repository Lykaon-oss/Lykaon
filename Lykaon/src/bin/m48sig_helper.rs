//! Test helper for the M4-8 signal cases (tests/m4.rs).
//!
//! args: <interrupt|stop|hangup> <source file>
//!
//! Fires the signal flag the way the OS would, then runs the file with the
//! ordinary harness rules and exits with the run's code (the program's own
//! words print first). The flag is process-global, so the test needs a
//! subprocess - this one.
//!
//! It is a real cargo binary (like the fuzz bins) instead of a raw `rustc`
//! link from the test: the rustc link searched stale target/debug/deps
//! artifacts and failed with E0460.

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    // the harness passes a leading `pre` marker (kept for compatibility
    // with the earlier rustc-built helper's argument shape)
    let args = match raw.first().map(|s| s.as_str()) {
        Some("pre") => &raw[1..],
        _ => &raw[..],
    };
    if args.len() < 2 {
        eprintln!("usage: m48sig_helper [pre] <interrupt|stop|hangup> <source file>");
        std::process::exit(2);
    }
    let sig = match args[0].as_str() {
        "interrupt" => lykaon::sem::SignalName::Interrupt,
        "stop" => lykaon::sem::SignalName::Stop,
        _ => lykaon::sem::SignalName::Hangup,
    };
    lykaon::signals::test_fire(sig);
    let src = match std::fs::read_to_string(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {}: {e}", args[1]);
            std::process::exit(1);
        }
    };
    let (out, code) = lykaon::run_source(&src, "sig48.lykaon", "");
    print!("{out}");
    std::process::exit(code);
}
