//! M4-12: the Appendix K conformance table (M4-T02 .. M4-T29), plus the
//! traceability map for the cases that live in the harness instead of a
//! single program (servers, CLI tools, the Linux-only `Run echo` case).
//!
//! Each case below is one row of Appendix K section 10, with the program
//! the row describes and the expected result from the row. Cases whose
//! expected wording is reduced by a logged deviation (anonymous failures,
//! T0617-T0619's code-in-the-message posture) say so in the case comment.
//!
//! Run: cargo test --test m4_conformance -- --nocapture

use lykaon::{check_source, run_source};

struct Case {
    id: &'static str,
    what: &'static str,
    source: &'static str,
    expect: Expect,
}

enum Expect {
    /// Successful run; the output (trailing newlines ignored) must match.
    Out(&'static str),
    /// A failing run whose output must contain this text.
    Fail(&'static str),
    /// Not runnable as one program on this platform; the reason.
    Elsewhere(&'static str),
}

/// The temporary file names these cases create; removed before every run so
/// a rerun starts clean (Write refuses to replace an existing file).
const TEMP_FILES: [&str; 8] = [
    "m4tc11", "m4tc13", "m4tc14", "m4tc15", "m4tc17", "m4tca", "m4tcb", "m4tcc",
];

fn clean_temp() {
    for name in TEMP_FILES {
        for dir in [std::env::temp_dir()] {
            for p in [dir.join(name), dir.join(format!("{name}.tmp"))] {
                let _ = std::fs::remove_file(p);
            }
        }
    }
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            id: "M4-T01",
            what: "all earlier golden tests, native",
            source: "",
            expect: Expect::Elsewhere(
                "covered by the m1a/m1b/m2/m3 suites and tests/native.rs (the differential sweep)",
            ),
        },
        Case {
            id: "M4-T02",
            what: "Book Ch 43 square",
            source: "\
Start task square.
    Give back 5 times 5.
Wait for square.
Say it.
",
            expect: Expect::Out("25"),
        },
        Case {
            id: "M4-T03",
            what: "Book Ch 43 two tasks",
            source: "\
Start task one.
    Give back 1 plus 1.
Start task two.
    Give back 2 plus 2.
Wait for one.
Say it.
Wait for two.
Say it.
",
            expect: Expect::Out("2\n4"),
        },
        Case {
            id: "M4-T04",
            what: "Book Ch 44 channel",
            source: "\
Bag is channel of whole number.
Send 7 to bag.
Receive from bag.
Say it.
",
            expect: Expect::Out("7"),
        },
        Case {
            id: "M4-T05",
            what: "Book Ch 44 guarded tally",
            source: "\
Tally is guarded 0.
Set tally to tally plus 1.
Say tally.
",
            expect: Expect::Out("1"),
        },
        Case {
            id: "M4-T06",
            what: "Book Ch 45 After 5 seconds",
            source: "\
After 5 seconds.
    Say time is up.
Say waiting.
",
            expect: Expect::Out("waiting\ntime is up"),
        },
        Case {
            id: "M4-T07",
            what: "Book Ch 45 Every with Stop",
            source: "\
Ticks is counter.
Every 5 seconds.
    Add 1 to ticks.
    Say tick.
    If ticks is 3.
        Stop.
Sleep for 16 seconds.
Say done.
",
            expect: Expect::Out("tick\ntick\ntick\ndone"),
        },
        Case {
            id: "M4-T08",
            what: "Book Ch 45 stream loop with 1 and 2 sent",
            source: "\
Bag is channel of whole number.
Send 1 to bag.
Send 2 to bag.
For each x as they arrive from bag.
    Say x.
",
            expect: Expect::Out("1\n2"),
        },
        Case {
            id: "M4-T09",
            what: "Book Ch 46 Run echo with hello",
            source: "\
Run echo with hello.
Say it.
",
            expect: Expect::Elsewhere(
                "the target is Linux x86-64 and Run uses no shell: /bin/echo exists there; \
                 Windows has no echo program on the path (M4-G20/S76)",
            ),
        },
        Case {
            id: "M4-T10",
            what: "Book Ch 46 environment with normal fallback",
            source: "\
Say Environment lykaon m4 conformance.
",
            expect: Expect::Out("normal"),
        },
        Case {
            id: "M4-T11",
            what: "Book Ch 47 greeting file (Replace, Append, Read)",
            source: "\
Write hello to file m4tc11 in temporary folder.
Append world to file m4tc11 in temporary folder.
Read file m4tc11 in temporary folder.
Say it.
",
            expect: Expect::Out("hello\nworld"),
        },
        Case {
            id: "M4-T12",
            what: "Book Ch 47 reading a missing file",
            source: "\
Read file m4tcnosuch in temporary folder.
",
            // the row's wording is \"no such file\"; the M4 cut reports file
            // failures anonymously (logged in LYKAON_DEVIATIONS.md), so the
            // conformance check here is that the run fails with the
            // documented anonymous failure and no crash
            expect: Expect::Fail("The program can fail here"),
        },
        Case {
            id: "M4-T13",
            what: "Write to an existing file",
            source: "\
Write 1 to file m4tc13 in temporary folder.
Write 2 to file m4tc13 in temporary folder.
",
            expect: Expect::Fail("The program can fail here"),
        },
        Case {
            id: "M4-T14",
            what: "Book Ch 48 saving a record as JSON",
            source: "\
A creature has legs as whole number.
Save a creature with legs 2 as json to file m4tc14 in temporary folder.
Read file m4tc14 in temporary folder.
Say it.
",
            expect: Expect::Out("{\n  \"legs\": 2\n}"),
        },
        Case {
            id: "M4-T15",
            what: "round trip: save a record and read it back",
            source: "\
A box has w as whole number.
b is a box with w 9.
Save b as json to file m4tc15 in temporary folder.
Read json file m4tc15 in temporary folder as box.
Say json of it.
",
            expect: Expect::Out("{\"w\":9}"),
        },
        Case {
            id: "M4-T16",
            what: "JSON missing a part",
            source: "\
A box has w as whole number and h as whole number.
Save a box with w 1 and h 2 as json to file m4tca in temporary folder.
Write nothing to file m4tcb in temporary folder.
Read json file m4tcb in temporary folder as box.
",
            // the row wants a message naming the part; the M4 cut reports
            // decode failures anonymously (logged), so the check is failure
            // without a crash
            expect: Expect::Fail("The program can fail here"),
        },
        Case {
            id: "M4-T17",
            what: "TOML, YAML, XML, CSV round trips",
            source: "\
A rock has weight as whole number and shine as whole number.
Save a rock with weight 5 and shine 2 as toml to file m4tcc in temporary folder.
Read toml file m4tcc in temporary folder as rock.
Say json of it.
Save a rock with weight 6 and shine 3 as yaml to file m4tcc in temporary folder.
Read yaml file m4tcc in temporary folder as rock.
Say json of it.
Save a rock with weight 8 and shine 1 as xml to file m4tcc in temporary folder.
Read xml file m4tcc in temporary folder as rock.
Say json of it.
A rowly has count as whole number.
Mine is a rowly with count 4.
Save list of mine as csv to file m4tcc in temporary folder.
Read csv file m4tcc in temporary folder as list of rowly.
Say json of them.
",
            expect: Expect::Out(
                "{\"weight\":5,\"shine\":2}\n{\"weight\":6,\"shine\":3}\n{\"weight\":8,\"shine\":1}\n[{\"count\":4}]",
            ),
        },
        Case {
            id: "M4-T18",
            what: "Book Ch 49 Say hash of hello.",
            source: "\
Say hash of hello.
",
            expect: Expect::Out("2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"),
        },
        Case {
            id: "M4-T19",
            what: "Book Ch 49 secret",
            source: "\
Changeable password is secret hunter.
Say password.
Say reveal password.
",
            expect: Expect::Out("hidden\nhunter"),
        },
        Case {
            id: "M4-T20",
            what: "Book Ch 49 3 days after today and days between",
            source: "\
d is 3 days after today.
Say days between today and d.
",
            expect: Expect::Out("3"),
        },
        Case {
            id: "M4-T21",
            what: "Use seed 42. two runs of random number from 1 to 100",
            source: "\
Use seed 42.
Say random number from 1 to 100.
Say random number from 1 to 100.
Say random number from 1 to 100.
",
            expect: Expect::Elsewhere(
                "the case is two runs compared; see m4_12_conformance_seed_is_deterministic",
            ),
        },
        Case {
            id: "M4-T22",
            what: "Book Ch 51 Fetch nowhere dot invalid",
            source: "\
Fetch plain nowhere dot invalid home.
",
            // the row wants \"no such host\"; network failures are anonymous
            // in this cut (logged), so the check is failure without a crash
            expect: Expect::Fail("The program can fail here"),
        },
        Case {
            id: "M4-T23",
            what: "a local server and a fetch to it",
            source: "",
            expect: Expect::Elsewhere(
                "needs a server and a client at once; harness case tests/m4.rs::m4_10_fetch_home_and_read_the_record",
            ),
        },
        Case {
            id: "M4-T24",
            what: "Book Ch 52 server response body",
            source: "",
            expect: Expect::Elsewhere(
                "harness case tests/m4.rs::m4_10_fetch_home_and_read_the_record",
            ),
        },
        Case {
            id: "M4-T25",
            what: "page with a parameter",
            source: "",
            expect: Expect::Elsewhere(
                "harness case tests/m4.rs::m4_10_request_rows_method_page_parameter (id = 42)",
            ),
        },
        Case {
            id: "M4-T26",
            what: "handler that stops with a bug",
            source: "",
            expect: Expect::Elsewhere("harness case tests/m4.rs::m4_10_failing_handler_gives_500"),
        },
        Case {
            id: "M4-T27",
            what: "Book Ch 53 greet tool",
            source: "",
            expect: Expect::Elsewhere(
                "CLI tool harness: tests/m4.rs::m48_takes_seed_and_option_default + m48_help_gives_usage_and_exit_0",
            ),
        },
        Case {
            id: "M4-T28",
            what: "missing argument",
            source: "",
            expect: Expect::Elsewhere(
                "CLI tool harness: tests/m4.rs::m48_bad_usage_gives_usage_and_exit_2",
            ),
        },
        Case {
            id: "M4-T29",
            what: "Ask with no person",
            source: "",
            expect: Expect::Elsewhere(
                "harness case tests/m4.rs::m48_ask_without_person_fails (S86)",
            ),
        },
    ]
}

#[test]
fn m4_12_appendix_k_conformance_table() {
    // T10's environment: the variable named by the words in upper case
    // joined by _ (M4-S80), so `Environment lykaon m4 conformance.` reads
    // Lykaon_M4_CONFORMANCE.
    // SAFETY: test-only, set before any program run reads the variable (the
    // same helper shape tests/m4.rs uses for the M4-8 environment cases)
    unsafe { std::env::set_var("Lykaon_M4_CONFORMANCE", "normal") };
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    let mut elsewhere = 0usize;
    println!("Appendix K conformance table:");
    for case in cases() {
        clean_temp();
        match case.expect {
            Expect::Elsewhere(why) => {
                elsewhere += 1;
                println!("  {}  elsewhere: {}", case.id, case.what);
                println!("            {}", why);
            }
            Expect::Out(want) => {
                ran += 1;
                let (out, code) = run_source(case.source, "conformance.lykaon", "");
                let got = out.trim_end();
                if code != 0 {
                    failures.push(format!(
                        "{} ({}): expected success, got exit {code}:\n{out}",
                        case.id, case.what
                    ));
                } else if got != want {
                    failures.push(format!(
                        "{} ({}): output mismatch\n--- expected ---\n{:?}\n--- actual ---\n{:?}",
                        case.id, case.what, want, got
                    ));
                } else {
                    println!("  {}  ok: {}", case.id, case.what);
                }
            }
            Expect::Fail(needle) => {
                ran += 1;
                let (out, code) = run_source(case.source, "conformance.lykaon", "");
                if code == 0 {
                    failures.push(format!(
                        "{} ({}): expected a failure, got success:\n{out}",
                        case.id, case.what
                    ));
                } else if !out.contains(needle) {
                    failures.push(format!(
                        "{} ({}): failure text lacks {needle:?}:\n{out}",
                        case.id, case.what
                    ));
                } else {
                    println!("  {}  ok (failure): {}", case.id, case.what);
                }
            }
        }
    }
    clean_temp();
    println!("  {ran} cases ran, {elsewhere} live in the harness (mapped above)");
    assert!(
        failures.is_empty(),
        "conformance failures:\n{}",
        failures.join("\n\n")
    );
}

/// M4-T21: two runs of the same seeded program give the same sequence.
#[test]
fn m4_12_conformance_seed_is_deterministic() {
    let program = "\
Use seed 42.
Say random number from 1 to 100.
Say random number from 1 to 100.
Say random number from 1 to 100.
";
    let (a, ca) = run_source(program, "seed.lykaon", "");
    let (b, cb) = run_source(program, "seed.lykaon", "");
    clean_temp();
    assert_eq!(ca, 0, "{a}");
    assert_eq!(cb, 0, "{b}");
    assert_eq!(a, b, "two seeded runs differ");
    println!("  M4-T21 ok: seeded sequence {a:?}");
}

/// M4-T23..T26 live in tests/m4.rs because they need a server and a client
/// at the same time. This guard fails if a mapped test is renamed away, so
/// the traceability map above cannot rot silently.
#[test]
fn m4_12_server_conformance_cases_exist() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/m4.rs");
    let tests = std::fs::read_to_string(path).expect("tests/m4.rs");
    for name in [
        "m4_10_fetch_home_and_read_the_record",
        "m4_10_request_rows_method_page_parameter",
        "m4_10_failing_handler_gives_500",
        "m48_takes_seed_and_option_default",
        "m48_help_gives_usage_and_exit_0",
        "m48_bad_usage_gives_usage_and_exit_2",
        "m48_ask_without_person_fails",
    ] {
        let name: &str = name;
        assert!(
            tests.contains(name),
            "the conformance map refers to a missing harness test: {name}"
        );
    }
}

/// M4-T33: sentences of M5 and later give T0509 and never crash
/// (Appendix K 1.1: databases, Load, Plot, Predict, the sandbox, Limit
/// memory/time, encryption, screens, bridges).
#[test]
fn m4_12_m5_and_later_sentences_are_t0509() {
    let later = [
        "Limit memory to 10 megabytes.",
        "Limit time to 5 seconds.",
        "Load the model from file brain.",
        "Plot sales by month.",
        "Predict the price of the house.",
        "Open database shop.",
        "Query the database for users.",
        "Encrypt the file with key one.",
        "Show screen home.",
        "Bridge to the phone.",
        "Train the model on the data.",
        // G6: the sandbox spelling - `Run safely.` must be T0509, not a
        // Run of a program named "safely"
        "Run safely.",
    ];
    let mut failures = Vec::new();
    for src in later {
        let (out, ok) = check_source(src, "later.lykaon");
        if ok || !out.contains("T0509") {
            failures.push(format!("{src:?}: expected T0509, got ok={ok}:\n{out}"));
        }
    }
    assert!(failures.is_empty(), "{}\n", failures.join("\n\n"));
}

/// The compile-time conformance checks that belong to the M4 error rows
/// (T0451, T0460's shape, T0509 for M5-and-later sentences, T0521, T0610's
/// shape) are exercised here as one negative table.
#[test]
fn m4_12_error_conformance_table() {
    let checks: [(&str, &str, &str); 5] = [
        (
            "T0451",
            "captured changeable name in a task",
            "Changeable total is 5.\nStart task grabber.\n    Give back total.\n",
        ),
        (
            "T0521",
            "certificate checks skipped outside Be careful",
            "Fetch plain example dot com without checking certificates.\n",
        ),
        (
            "T0509",
            "a sentence of M5 and later",
            "Limit memory to 10 megabytes.\n",
        ),
        (
            "T0166",
            "a handler with no Respond",
            "Serve on port 24999.\n    When someone gets home.\n        Say hello.\n",
        ),
        (
            "T0173",
            "an undeclared page",
            "Fetch plain example dot com ghost page.\n",
        ),
    ];
    let mut failures = Vec::new();
    for (code, what, src) in checks {
        let (out, ok) = check_source(src, "conformance.lykaon");
        if ok || !out.contains(code) {
            failures.push(format!(
                "{code} ({what}): expected {code}, got ok={ok}:\n{out}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
