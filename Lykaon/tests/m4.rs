//! M4 (Appendix K) milestone tests - first increment: task sentences.
//! Grammar: Start task NAME. / Wait for NAME. / Do these together. /
//! Stop task NAME. / Sleep for NUMBER <unit>.
//! Execution: the eager first cut - a task runs at its Start task sentence
//! on the starting worker; Wait for takes the stored result once (a copy-kind
//! result copies and a second wait is allowed). Capture checks: a task body
//! reads fixed names, a Changeable capture is T0451. Waiting for a name that
//! is not a task is T0168.

use lykaon::{check_source, run_source, run_source_tool};

fn run(src: &str) -> (String, i32) {
    run_source(src, "program.lykaon", "")
}

fn trim(s: &str) -> String {
    s.trim_end().to_string()
}

/// M4-S2 / T0450 (the book's "a plain list used by two tasks"): a task body
/// may not carry a plain move-kind value from outside into the task. The
/// caret sits on the body sentence, under the value's name.
#[test]
fn m4_s2_value_crossing_tasks_is_t0450() {
    let src = "\
Items is list of 1 and 2 and 3.
Start task looker.
    Say items.
";
    let (out, ok) = check_source(src, "program.lykaon");
    assert!(!ok, "expected a diagnostic, got: {out}");
    assert!(out.contains("T0450"), "expected T0450, got: {out}");
    assert!(
        out.contains("Value crosses tasks unsafely."),
        "expected the book's name, got: {out}"
    );
    assert!(
        out.contains("A value that is not given, shared and immutable, guarded or atomic goes to another task."),
        "expected the book's cause, got: {out}"
    );
    assert!(
        out.contains("Give it, share it or guard it."),
        "expected the book's fix, got: {out}"
    );
    assert!(
        out.contains("line 3: Say items."),
        "the mark must sit on the reading sentence, got: {out}"
    );
}

/// M4-S2 / T0462: the name of a started task is its handle; storing it in a
/// collection keeps it past the block and is refused.
#[test]
fn m4_s2_task_handle_stored_is_t0462() {
    let src = "\
Changeable watchers is list of nothing.
Start task looker.
    Say ready.
Add looker to watchers.
Wait for looker.
";
    let (out, ok) = check_source(src, "program.lykaon");
    assert!(!ok, "expected a diagnostic, got: {out}");
    assert!(out.contains("T0462"), "expected T0462, got: {out}");
    assert!(
        out.contains("Task outlives its block."),
        "expected the book's name, got: {out}"
    );
    assert!(
        out.contains("A task name or a task handle is returned or stored outside its block."),
        "expected the book's cause, got: {out}"
    );
    assert!(
        out.contains("Wait for it inside the block."),
        "expected the book's fix, got: {out}"
    );
    // the task name is a task, not an undefined value: only T0462 reports
    assert!(
        !out.contains("T0205"),
        "the name must not also be undefined: {out}"
    );
}

/// T0462's other shape: returning the handle out of a function.
#[test]
fn m4_s2_task_handle_returned_is_t0462() {
    let src = "\
To watch this.
    Start task looker.
        Say ready.
    Give back looker.
Say watch 1.
";
    let (out, ok) = check_source(src, "program.lykaon");
    assert!(!ok, "expected a diagnostic, got: {out}");
    assert!(out.contains("T0462"), "expected T0462, got: {out}");
    assert!(out.contains("line 4: Give back looker."), "{out}");
}

/// T0462's control: waiting for the task inside its block is the allowed use.
#[test]
fn m4_s2_task_waited_inside_block_cleanly() {
    let (out, code) = run("\
Start task looker.
    Say ready.
Wait for looker.
Say done.
");
    assert_eq!(code, 0, "waiting inside the block must be allowed: {out}");
    assert!(!out.contains("T0462"), "{out}");
    assert!(out.contains("ready"), "{out}");
}

/// T0450's controls: the three ways the book allows the value across (given,
/// shared, or a copy-kind value) must stay clean, or the check has widened.
#[test]
fn m4_s2_given_value_crosses_tasks_cleanly() {
    let (out, code) = run("\
Items is list of 1 and 2 and 3.
Start task looker.
    Give back items.
Wait for looker.
");
    assert_eq!(code, 0, "giving the value must be allowed: {out}");
    assert!(!out.contains("T0450"), "{out}");
}

#[test]
fn m4_s2_shared_value_crosses_tasks_cleanly() {
    let (out, code) = run("\
Items is list of 1 and 2 and 3.
Share items.
Start task looker.
    Say items.
Wait for looker.
");
    assert_eq!(code, 0, "sharing the value must be allowed: {out}");
    assert!(!out.contains("T0450"), "{out}");
    assert_eq!(trim(&out), "1, 2 and 3");
}

#[test]
fn m4_s2_copy_value_crosses_tasks_cleanly() {
    let (out, code) = run("\
Count is 5.
Start task looker.
    Say count.
Wait for looker.
");
    assert_eq!(code, 0, "a copy-kind value must be allowed: {out}");
    assert!(!out.contains("T0450"), "{out}");
    assert_eq!(trim(&out), "5");
}

/// M4-S14 / T0609: Close a channel, then Send on it. The closed flag is
/// real state, so the Send is a program-stopping error with the book's
/// wording.
#[test]
fn m4_send_on_a_closed_channel_is_t0609() {
    let (out, code) = run("\
Bag is channel of whole number.
Try Close bag.
If that fails.
    Say nothing.
Send 5 to bag.
");
    assert_ne!(code, 0, "expected a failure, got: {out}");
    assert!(out.contains("T0609"), "expected T0609, got: {out}");
    assert!(
        out.contains("A value was sent on a channel with no receivers."),
        "expected the book's cause, got: {out}"
    );
}

/// T0618: Serve cannot listen. The test holds the port itself, so the
/// program's Serve meets a port already in use.
#[test]
fn m4_port_in_use_is_t0618() {
    let held = std::net::TcpListener::bind(("0.0.0.0", 0)).expect("test listener");
    let port = held.local_addr().expect("local addr").port();
    let (out, code) = run(&format!(
        "\
Serve on port {port}.
    When someone gets home.
        Respond with status 200 and text hello.
"
    ));
    drop(held);
    assert_ne!(code, 0, "expected a failure, got: {out}");
    assert!(out.contains("T0618"), "expected T0618, got: {out}");
    assert!(
        out.contains("Serve cannot listen."),
        "expected the book's cause, got: {out}"
    );
}

/// T0619: a certificate the run cannot use. The files do not exist, so the
/// Serve's TLS setup fails with the book's wording (the TLS feature is on by
/// default; the native runtime logs its own limitation).
#[test]
fn m4_refused_certificate_is_t0619() {
    #[cfg(feature = "tls")]
    {
        let (out, code) = run("\
Serve securely on port 24998 using certificate file named missingpem and key file named missingkey.
    When someone gets home.
        Respond with status 200 and text hello.
");
        assert_ne!(code, 0, "expected a failure, got: {out}");
        assert!(out.contains("T0619"), "expected T0619, got: {out}");
        assert!(
            out.contains("TLS verification failed."),
            "expected the book's cause, got: {out}"
        );
    }
}

#[test]
fn m4_task_gives_back_via_wait() {
    let (out, code) = run("\
Start task helper2.
    Give back 21 plus 21.
Wait for helper2.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "42");
}

#[test]
fn m4_task_captures_a_fixed_name() {
    // M4-S2 first cut: a task may capture a fixed name.
    let (out, code) = run("\
greeting is 7.
Start task helper2.
    Give back greeting.
Wait for helper2.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_changeable_capture_is_t0451() {
    // M4-S2 / T0451: a task may not capture a Changeable name.
    let (out, ok) = check_source(
        "\
Changeable total is 5.
Start task grabber.
    Give back total.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0451"), "expected T0451, got: {out}");
}

#[test]
fn m4_wait_for_unknown_name_is_t0168() {
    let (out, ok) = check_source(
        "\
Wait for ghost.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0168"), "expected T0168, got: {out}");
}

#[test]
fn m4_do_together_is_transparent_for_task_names() {
    // M4-D2: the task name defined inside Do these together stays visible
    // after the block, so Wait for maker. finds it.
    let (out, code) = run("\
Do these together.
    Start task maker.
        Give back 11.
Wait for maker.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "11");
}

#[test]
fn m4_copy_result_survives_a_second_wait() {
    // M4-D14: a copy kind copies, so a second Wait for is allowed.
    let (out, code) = run("\
Start task giver.
    Give back 12.
Wait for giver.
Wait for giver.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "12");
}

#[test]
fn m4_moved_result_taken_twice_is_t0334() {
    // M4-D14: a move-kind result (a list moves) is gone after the first
    // take, so the second wait is T0334.
    let (out, code) = run("\
items is list of 1 and 2 and 3.
Start task giver.
    Give back items.
Wait for giver.
Wait for giver.
");
    assert_ne!(code, 0, "second wait must fail, got: {out}");
    assert!(out.contains("T0334"), "expected T0334, got: {out}");
}

#[test]
fn m4_sleep_runs_on_the_pause_list() {
    // M4-G4/G5/G6: Sleep for NUMBER <unit>. pauses and goes on.
    let (out, code) = run("\
Changeable count is 1.
Sleep for 1 milliseconds.
Set count to count plus 1.
Say count.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "2");
}

#[test]
fn m4_sleep_needs_a_number_and_a_unit() {
    let (out, ok) = check_source("Sleep for soon.\n", "program.lykaon");
    assert!(!ok, "expected a compile error, got: {out}");
    let (out2, ok2) = check_source("Sleep for 5 fortnights.\n", "program.lykaon");
    assert!(!ok2, "expected a compile error, got: {out2}");
    // both must be honest diagnostics, not crashes
    assert!(!out.is_empty() && !out2.is_empty());
}

#[test]
fn m4_stop_task_on_a_finished_task_is_a_no_op() {
    // M4-S7 first cut: eager tasks have already ended, so the cancel
    // request is harmless and the result is still there for Wait for.
    let (out, code) = run("\
Start task worker.
    Give back 9.
Stop task worker.
Wait for worker.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "9");
}

#[test]
fn m4_task_body_sentences_run() {
    // a task body is a normal block: its sentences run
    let (out, code) = run("\
Start task talker2.
    Say 5.
Wait for talker2.
Say 6.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "5\n6");
}

// ===== M4-3: channels, guarded, atomic, counter (Appendix K 7.1/7.2) =====

#[test]
fn m4_channel_send_then_receive() {
    // M4-G7/G11/G12 + M4-S13: the received value is it.
    let (out, code) = run("\
Bag is channel of whole number.
Send 42 to bag.
Receive from bag.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "42");
}

#[test]
fn m4_channel_keeps_order() {
    // M4-S12: items come out of a channel in the order they went in.
    let (out, code) = run("\
Bag is channel of whole number.
Send 1 to bag.
Send 2 to bag.
Send 3 to bag.
Receive from bag.
Say it.
Receive from bag.
Say it.
Receive from bag.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "1\n2\n3");
}

#[test]
fn m4_channel_captured_by_a_task() {
    // M4-S15: both ends are in the one name; a task that captured the
    // channel sends into the SAME queue (the Rc shares the state).
    let (out, code) = run("\
Bag is channel of whole number.
Start task filler.
    Send 7 to bag.
Wait for filler.
Receive from bag.
Say it.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_receive_from_empty_channel_is_a_deadlock_report() {
    // M4-S11: Receive pauses when the channel is empty. In the eager
    // first cut nothing can wake the pause, so it is a deadlock report
    // (T0610 family); the exact behavior is logged as a deviation.
    let (out, code) = run("\
Bag is channel of whole number.
Receive from bag.
");
    assert_ne!(code, 0, "expected a failure, got: {out}");
    assert!(out.contains("T0610"), "expected T0610, got: {out}");
}

#[test]
fn m4_send_on_a_full_channel_is_a_deadlock_report() {
    // M4-S11: Send pauses when the channel is full; eager cut = deadlock
    // report. holding 1 takes the queue to capacity after one send.
    let (out, code) = run("\
Bag is channel of whole number holding 1.
Send 1 to bag.
Send 2 to bag.
");
    assert_ne!(code, 0, "expected a failure, got: {out}");
    assert!(out.contains("T0610"), "expected T0610, got: {out}");
}

#[test]
fn m4_holding_outside_the_window_is_refused() {
    // M4-S11: N goes from 1 to 1,000,000; anything else cannot be read.
    let (out, ok) = check_source(
        "\
Bag is channel of whole number holding 2000000.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0113"), "expected T0113, got: {out}");
}

#[test]
fn m4_send_to_a_non_channel_is_reordered() {
    // M4-G11: Send names a channel; a list or a name that does not
    // exist is refused before it can run.
    let (out, ok) = check_source(
        "\
Bag is Changeable list of 1 and 2.
Send 3 to bag.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0169"), "expected T0169, got: {out}");
    let (out2, ok2) = check_source("Send 5 to bag.\n", "program.lykaon");
    assert!(!ok2, "expected a compile error, got: {out2}");
}

#[test]
fn m4_counter_adds_and_prints() {
    // M4-G10 + M4-S20: a counter starts at 0 and Add adds; Say prints
    // the value.
    let (out, code) = run("\
Hits is counter.
Add 1 to hits.
Add 4 to hits.
Say hits.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "5");
}

#[test]
fn m4_counter_in_a_task() {
    // a counter captured by a task adds in that task; the value is
    // readable right after (the eager cut runs the body at Start task).
    let (out, code) = run("\
Hits is counter.
Start task clicker.
    Add 2 to hits.
Wait for clicker.
Say hits.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "2");
}

#[test]
fn m4_atomic_add_atomically_is_one_step() {
    // M4-G9 + M4-G13 + M4-S19: an atomic number starts at 0 and changes
    // with Add ... atomically.
    let (out, code) = run("\
N is atomic number.
Add 5 to N atomically.
Add 2 to N atomically.
Say N.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_add_atomically_on_a_plain_name_is_refused() {
    // M4-G13: only an atomic number or a counter changes with Add
    // atomically; a Changeable whole number needs Set.
    let (out, code) = run("\
N is Changeable 5.
Add 2 to N atomically.
");
    assert_ne!(code, 0, "expected a failure, got: {out}");
    assert!(out.contains("T0406"), "expected T0406, got: {out}");
}

#[test]
fn m4_guarded_set_changes_the_inner_value() {
    // M4-G8 + M4-S16 + M4-D3: a guarded name is fixed but changes
    // through Set; each Set is one sentence and one lock.
    let (out, code) = run("\
Tally is guarded 0.
Set tally to tally plus 1.
Set tally to tally plus 10.
Say tally.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "11");
}

#[test]
fn m4_guarded_set_inside_a_task() {
    // M4-D3 + M4-S2: a task captures a guarded name and Sets it.
    let (out, code) = run("\
Tally is guarded 0.
Start task bump.
    Set tally to tally plus 5.
Wait for bump.
Say tally.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "5");
}

#[test]
fn m4_set_on_a_counter_is_refused_at_compile_time() {
    // M4-D3: an atomic or counter changes with Add, never with Set.
    let (out, ok) = check_source(
        "\
Hits is counter.
Set hits to 3.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0406"), "expected T0406, got: {out}");
}

// ===================================================== M4-4 (G14..G18)

#[test]
fn m4_after_fires_at_main_end_in_order() {
    // M4-G14 + M4-S25 + M4-S28: After starts a one-shot timer and goes on;
    // the program does not end while the timer is pending - at main end
    // the pending After fires (real sleep to the deadline).
    let (out, code) = run("\
After 40 milliseconds.
    Say later.
Say immediately.
");
    assert_eq!(code, 0);
    assert_eq!(trim(&out), "immediately\nlater");
}

#[test]
fn m4_every_runs_fixed_rate_rounds_during_a_sleep() {
    // M4-G15 + M4-D12: Every 30 milliseconds. runs a round each 30 ms from
    // the START of a round, never overlapping; one 100 ms sleep holds the
    // rounds that start within it (3 or 4 with jitter: the fourth round
    // may start at the sleep boundary).
    let (out, code) = run("\
Hits is counter.
Every 30 milliseconds.
    Add 1 to hits.
Sleep for 100 milliseconds.
Say hits.
");
    assert_eq!(code, 0, "{out}");
    let n: i64 = trim(&out)
        .parse()
        .unwrap_or_else(|_| panic!("expected a count, got: {out}"));
    assert!((3..=4).contains(&n), "expected 3 or 4 rounds, got: {out}");
}

#[test]
fn m4_stop_inside_an_every_ends_it() {
    // M4-S26: Stop. inside a round ends the Every - later rounds do not
    // run even while the program keeps sleeping.
    let (out, code) = run("\
Hits is counter.
Every 20 milliseconds.
    Add 1 to hits.
    If hits is 2.
        Stop.
Sleep for 200 milliseconds.
Say hits.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "2");
}

#[test]
fn m4_stream_loop_drains_the_channel() {
    // M4-G16 + M4-S27: For each x as they arrive from bag. receives the
    // queued values in order (the eager cut drains the queue); x is the
    // value in the body. When nothing is left, the loop ends.
    let (out, code) = run("\
Bag is channel of whole number.
Send 1 to bag.
Send 2 to bag.
Send 3 to bag.
Changeable total is 0.
For each x as they arrive from bag.
    Set total to total plus x.
Say total.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "6");
}

#[test]
fn m4_stream_loop_target_not_a_channel_is_t0168() {
    // T0168: the stream loop names a channel, not any list.
    let (out, ok) = check_source(
        "\
Nums is list of 1 and 2.
For each x as they arrive from nums.
    Say x.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0168"), "expected T0168, got: {out}");
}

#[test]
fn m4_spread_collects_into_them_in_item_order() {
    // M4-G18 + M4-S23: the block runs once per item; it is the item; the
    // given values collect into them in item order (worker count is
    // unobservable in the eager cut).
    let (out, code) = run("\
Nums is list of 1 and 2 and 3.
Changeable total is 0.
Spread each of nums over workers.
    Give back it times 10.
For each r in them.
    Set total to total plus r.
Say total.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "60");
}

#[test]
fn m4_use_workers_precedes_spread_sentences() {
    // M4-S22 + M4-G17: Use 4 workers. sets the count for the Spread
    // sentences that follow in this block; the spread still collects its
    // results in order in the eager cut.
    let (out, code) = run("\
Nums is list of 1 and 2.
Use 4 workers.
Changeable total is 0.
Spread each of nums over workers.
    Give back it times 3.
For each r in them.
    Set total to total plus r.
Say total.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "9");
}

#[test]
fn m4_use_workers_outside_the_window_is_refused() {
    // M4-S22: the number is 1 to 256 (no book code; T0113 reused).
    for n in [0, 257] {
        let (out, ok) = check_source(
            &format!(
                "\
Use {n} workers.
"
            ),
            "program.lykaon",
        );
        assert!(!ok, "expected a compile error for {n}, got: {out}");
        assert!(out.contains("T0113"), "expected T0113 for {n}, got: {out}");
    }
}

#[test]
fn m4_failure_inside_a_spread_stops_the_rest_and_propagates() {
    // M4-S24: a failure inside stops the other workers and is the failure
    // of the Spread sentence. Unhandled, the run reports the failure (the
    // T0311 wiring status for unhandled spread failures is logged in
    // LYKAON_DEVIATIONS.md for M4-4).
    let (out, code) = run("\
Nums is list of 1 and 2 and 3.
Spread each of nums over workers.
    Say it.
    Give back caught as whole number.
");
    assert_ne!(
        code, 0,
        "expected the run to report the failure, got: {out}"
    );
    // the first round's Say ran; the rest did not
    assert!(
        trim(&out).contains("1"),
        "expected item 1 printed, got: {out}"
    );
    assert!(
        !trim(&out).contains("2"),
        "items after the failure must not run, got: {out}"
    );
}

// ==================================================================
// M4-5 (Appendix K 7.5): files and paths.
// M4-G28..G48: the file sentences run through the embedded evaluator
// (deviation logged); failures are anonymous at run time (the Ask
// precedent, deviation logged), so a failing run reads
// "The program can fail here, and no fallback was written.".
// Every program works inside `in temporary folder` so no test touches
// the working directory, and each holds its own file names so parallel
// test processes cannot collide.

// The Write sentence refuses to overwrite (M4-S34), so a rerun of the
// suite must not inherit the leftovers of an earlier one: each
// Write-first test cleans its own names straight out of the temporary
// folder before its program runs. Removing a missing or wrong-kind
// name fails silently, which is exactly what a cleanup wants.
fn clean(names: &[&str]) {
    let t = std::env::temp_dir();
    for n in names {
        let p = t.join(n);
        let _ = std::fs::remove_file(&p);
        let _ = std::fs::remove_dir_all(&p);
    }
}

#[test]
fn m4_write_then_read_gives_back_the_text() {
    clean(&["mf55"]);
    let (out, code) = run("\
Write 42 to file mf55 in temporary folder.
Read file mf55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    // M4-S35: the text is written with one line feed; M4-S36: the read
    // keeps line endings, so Say adds nothing (the text ends with one).
    assert_eq!(trim(&out), "42");
}

#[test]
fn m4_append_creates_the_file_and_continues() {
    // M4-S34: Append creates the file when needed.
    clean(&["ma55"]);
    let (out, code) = run("\
Append 7 to file ma55 in temporary folder.
Read file ma55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_write_over_an_existing_file_fails() {
    // M4-S34: Write refuses to replace; Replace creates or overwrites.
    let (out, code) = run("\
Write 1 to file mw55 in temporary folder.
Write 1 to file mw55 in temporary folder.
");
    assert_ne!(code, 0, "{out}");
    assert!(out.contains("can fail here"), "{out}");
}

#[test]
fn m4_replace_overwrites_the_file() {
    clean(&["mr55"]);
    let (out, code) = run("\
Write 1 to file mr55 in temporary folder.
Replace file mr55 in temporary folder with 2.
Read file mr55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "2");
}

#[test]
fn m4_a_list_writes_one_line_per_item() {
    // M4-S35: a list of values writes each item as one line of its
    // shown wording.
    clean(&["ml55"]);
    let (out, code) = run("\
Write list of 7 and 8 and 9 to file ml55 in temporary folder.
Read file ml55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "7\n8\n9");
}

#[test]
fn m4_for_each_line_gives_lines_without_their_endings() {
    // M4-S36: For each line in file streams the lines without LF/CRLF.
    clean(&["mfl55"]);
    let (out, code) = run("\
Write list of 1 and 2 and 3 to file mfl55 in temporary folder.
For each line in file mfl55 in temporary folder.
    Say line.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "1\n2\n3");
}

#[test]
fn m4_read_bytes_of_gives_the_byte_values() {
    // M4-G35: the bytes of the file as a list of whole numbers (one
    // digit text: byte 49 and the line feed 10).
    clean(&["mb55"]);
    let (out, code) = run("\
Write 1 to file mb55 in temporary folder.
Read bytes of file mb55 in temporary folder.
For each b in them.
    Say b.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "49\n10");
}

#[test]
fn m4_reading_a_missing_file_is_an_anonymous_failure() {
    // M4-S37: a missing file is a not-found failure; the first cut
    // reports it anonymously (Ask precedent, deviation logged).
    let (out, code) = run("\
Read file mnothing55 in temporary folder.
");
    assert_ne!(code, 0, "{out}");
    assert!(out.contains("can fail here"), "{out}");
}

#[test]
fn m4_folders_make_list_and_remove() {
    // M4-G40/G44/G41: Make folder, List files in (sorted), Remove of a
    // folder removes it and what it holds.
    clean(&["mf56", "aa", "zz"]);
    let (out, code) = run("\
Make folder mf56 in temporary folder.
Write 1 to file zz in folder mf56 in temporary folder.
Write 2 to file aa in folder mf56 in temporary folder.
List files in folder mf56 in temporary folder.
For each f in them.
    Say f.
Remove folder mf56 in temporary folder.
If folder mf56 in temporary folder exists.
    Say 9.
");
    assert_eq!(code, 0, "{out}");
    // the listing is sorted by name, and the folder is gone after Remove
    assert_eq!(trim(&out), "aa\nzz");
}

#[test]
fn m4_move_and_duplicate_file() {
    // M4-G42/G43: Move file to file, Duplicate file as file.
    clean(&["mv55", "mvb55", "mvd55"]);
    let (out, code) = run("\
Write 7 to file mv55 in temporary folder.
Move file mv55 in temporary folder to file mvb55 in temporary folder.
Duplicate file mvb55 in temporary folder as file mvd55 in temporary folder.
Read file mvd55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_the_exists_question_answers_yes_and_no() {
    // M4-G45: file F exists is a yes-or-no question without a
    // comparison.
    clean(&["me55"]);
    let (out, code) = run("\
Write 1 to file me55 in temporary folder.
If file me55 in temporary folder exists.
    Say 1.
Remove file me55 in temporary folder.
If file me55 in temporary folder exists.
    Say 33.
Otherwise.
    Say 2.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "1\n2");
}

#[test]
fn m4_a_temporary_file_is_written_and_read_by_its_name() {
    // M4-G46/S38: Make temporary file NAME. binds a fresh file (removed
    // when the block that holds it ends); the binding wins over a
    // literal reading (logged).
    let (out, code) = run("\
Make temporary file scratch.
Write 11 to file scratch.
Read file scratch.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "11");
}

#[test]
fn m4_a_temporary_file_name_is_defined_once() {
    // T0207: the same temporary file name is not defined twice.
    let (out, ok) = check_source(
        "\
Make temporary file scratch.
Make temporary file scratch.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0207"), "expected T0207, got: {out}");
}

#[test]
fn m4_the_watcher_runs_its_block_on_a_change() {
    // M4-G47/S39: When file F changes. runs the block per change event
    // (changes closer than 100 milliseconds merge); the eager cut polls
    // during the Sleep pauses (deviation logged). One change means one
    // firing: never zero, and the merged cut can only fire it once.
    // The second write replaces the one-digit line with a two-digit
    // one, so the length itself changes: the poll catches the change
    // no matter how the file system quantizes modification times.
    let (out, code) = run("\
Make temporary file wend.
Write 1 to file wend.
When file wend changes.
    Say 77.
Replace file wend in temporary folder with 22.
Sleep for 500 milliseconds.
Say 88.
");
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("77"), "the watcher never fired: {out}");
    let fires = out.matches("77").count();
    assert!(fires == 1, "one change, so one firing, got {fires}: {out}");
}

#[test]
fn m4_zip_unzip_round_trip() {
    // M4-S41: Zip writes a deflate archive (sorted entries, fixed
    // stamp); Unzip restores the files, and the contents read back.
    clean(&["mz55", "seven", "pack55", "mback55"]);
    let (out, code) = run("\
Make folder mz55 in temporary folder.
Write 77 to file seven in folder mz55 in temporary folder.
Zip folder mz55 in temporary folder to file pack55 in temporary folder.
Remove folder mz55 in temporary folder.
Unzip file pack55 in temporary folder to folder mback55 in temporary folder.
Read file seven in folder mback55 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "77");
}

#[test]
fn m4_gzip_writes_a_gzip_stream() {
    // M4-S41: Gzip writes one gzip stream (the compressed file exists;
    // reading it back is a later increment, it is outside this grammar).
    clean(&["mg55", "mgz55"]);
    let (out, code) = run("\
Write 1 to file mg55 in temporary folder.
Gzip file mg55 in temporary folder to file mgz55 in temporary folder.
If file mgz55 in temporary folder exists.
    Say 1.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "1");
}

#[test]
fn m4_the_plain_remove_reading_still_works() {
    // Remove <value> from <coll>. keeps the M2 reading now that the
    // file reading shares the word. Removing is a change, so the
    // collection is Changeable (a fixed list refuses the remove).
    let (out, code) = run("\
Changeable nums is list of 1 and 2 and 3.
Remove 2 from nums.
For each n in nums.
    Say n.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "1\n3");
}

// ============================================================================
// M4-6 (Appendix K 7.6): the typed formats. Read json/toml/yaml/xml/csv
// file F as T. leaves the decoded value in it; Save <value> as <fw> to
// file F. writes the encoding (json pretty + one line feed; the other
// formats their doc shapes, logged). Failures are the ordinary
// anonymous runtime failure (deviation logged). The test values stay
// numeric (text literals in operand positions are a known parser cut),
// so the record parts below are whole numbers only.
// Every file name is unique per test and cleaned first, and every file
// sentence says in temporary folder.
// ============================================================================

#[test]
fn m4_json_of_gives_the_compact_text() {
    // M4-6/S46: json of x in expression position, compact spacing.
    let (out, code) = run("\
Say json of list of 1 and 2.
Say json of 5.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "[1,2]\n5");
}

#[test]
fn m4_json_of_a_record_holds_its_parts() {
    // M4-S46: a record writes its parts in declaration order (S43 key
    // words joined by _), compact.
    let (out, code) = run("\
A creature has legs as whole number and eyes as whole number.
Critter is a creature with legs 4 and eyes 2.
Say json of critter.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"legs\":4,\"eyes\":2}");
}

#[test]
fn m4_json_whole_number_round_trip() {
    // M4-S42/S46: Save writes the file, Read json file F as T. decodes
    // it.
    clean(&["fjq1"]);
    let (out, code) = run("\
Save 42 as json to file fjq1 in temporary folder.
Read json file fjq1 in temporary folder as whole number.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "42");
}

#[test]
fn m4_json_record_round_trip_reads_back_its_parts() {
    // the decoded value round-trips back through json of it (part reads
    // of it need a known kind, so the json view is the assertion)
    clean(&["fjr1"]);
    let (out, code) = run("\
A creature has legs as whole number and eyes as whole number.
Save a creature with legs 3 and eyes 1 as json to file fjr1 in temporary folder.
Read json file fjr1 in temporary folder as creature.
Say json of it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"legs\":3,\"eyes\":1}");
}

#[test]
fn m4_json_save_writes_pretty_with_a_final_line_feed() {
    // M4-S46: json saves pretty with two spaces per level and a line
    // feed at the end; Read file gives the text back verbatim.
    clean(&["fjp1"]);
    let (out, code) = run("\
A creature has legs as whole number.
Save a creature with legs 2 as json to file fjp1 in temporary folder.
Read file fjp1 in temporary folder.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\n  \"legs\": 2\n}");
}

#[test]
fn m4_json_from_text_chain_decodes() {
    // `Read json from text <value> as T.` decodes a text value; the
    // text comes from it here (a plain read of the written file).
    clean(&["fjt1"]);
    let (out, code) = run("\
Write 7 to file fjt1 in temporary folder.
Read file fjt1 in temporary folder.
Read json from text it as whole number.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "7");
}

#[test]
fn m4_json_enum_round_trip() {
    // M4-S45: an enum decodes from an object whose kind key holds the
    // variant name (words joined _); a partless variant needs the kind
    // key alone. Save writes the same shape.
    clean(&["fje1"]);
    let (out, code) = run("\
A mood is calm or wild.
Save wild as json to file fje1 in temporary folder.
Read json file fje1 in temporary folder as mood.
Say it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "wild");
}

#[test]
fn m4_json_enum_with_parts_round_trip() {
    // M4-S45: a variant with parts holds them in the object (the
    // part0.. spelling of the cut, logged).
    clean(&["fje2"]);
    let (out, code) = run("\
A cash is sum with total as whole number.
Save sum with total 9 as json to file fje2 in temporary folder.
Read json file fje2 in temporary folder as cash.
Say json of it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"kind\":\"sum\",\"part0\":9}");
}

#[test]
fn m4_bad_json_is_the_anonymous_failure() {
    // M4-S42: bad format fails at run time; the first cut gives the
    // ordinary anonymous failure wording (deviation logged).
    clean(&["fjbad"]);
    let (out, code) = run("\
Write hello to file fjbad in temporary folder.
Read json file fjbad in temporary folder as whole number.
Say 5.
");
    assert_ne!(code, 0, "{out}");
    assert!(out.contains("can fail here"), "{out}");
}

#[test]
fn m4_toml_record_round_trip() {
    // M4-6/S45: toml writes scalar parts as key = value lines and reads
    // them back into the record; the json view asserts the decode.
    clean(&["ftm1"]);
    let (out, code) = run("\
A rock has weight as whole number and shine as whole number.
Save a rock with weight 5 and shine 2 as toml to file ftm1 in temporary folder.
Read toml file ftm1 in temporary folder as rock.
Say json of it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"weight\":5,\"shine\":2}");
}

#[test]
fn m4_yaml_record_round_trip() {
    clean(&["fy1"]);
    let (out, code) = run("\
A rock has weight as whole number and shine as whole number.
Save a rock with weight 6 and shine 3 as yaml to file fy1 in temporary folder.
Read yaml file fy1 in temporary folder as rock.
Say json of it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"weight\":6,\"shine\":3}");
}

#[test]
fn m4_xml_record_round_trip() {
    // M4-6: xml writes the record as one element named like the kind,
    // one child per part, text content.
    clean(&["fx1"]);
    let (out, code) = run("\
A rock has weight as whole number.
Save a rock with weight 8 as xml to file fx1 in temporary folder.
Read xml file fx1 in temporary folder as rock.
Say json of it.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "{\"weight\":8}");
}

#[test]
fn m4_csv_list_of_records_round_trip() {
    // M4-S47: csv needs a header row whose names are the parts' names;
    // the target is a list of one record kind. The list comes from a
    // named record value (a ctor inside list of is a parser cut).
    clean(&["fc5"]);
    let (out, code) = run("\
A rowly has count as whole number.
Mine is a rowly with count 4.
Save list of mine as csv to file fc5 in temporary folder.
Read csv file fc5 in temporary folder as list of rowly.
Say json of them.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "[{\"count\":4}]");
}

#[test]
fn m4_csv_into_a_wrong_kind_is_a_shape_error() {
    // M4-S42 compile check: csv takes a list of one record kind only.
    let (out, ok) = check_source(
        "\
Read csv file fc6 in temporary folder as whole number.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
}

// ===================================================== M4-7 (S50..S57)

#[test]
fn m47_date_ctor_prints_iso() {
    // M4-S50/G54: date 2026 and 10 and 31 is 31 October 2026 and prints
    // 2026-10-31.
    let (out, code) = run("\
Changeable d is date 2026 and 10 and 31.
Say d.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "2026-10-31");
}

#[test]
fn m47_impossible_date_is_t0620() {
    // M4-S50: an impossible date is a bug (T0620) at compile time.
    let (out, ok) = check_source(
        "\
Changeable d is date 2026 and 2 and 30.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0620"), "expected T0620, got: {out}");
}

#[test]
fn m47_today_is_a_date_value() {
    // M4-S54: today is the date in the local zone; it prints the ISO
    // calendar day.
    let (out, code) = run("Say today.\n");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    assert_eq!(t.len(), 10, "today prints an ISO date, got: {t}");
    assert_eq!(t.as_bytes()[4], b'-', "today prints an ISO date, got: {t}");
}

#[test]
fn m47_moment_prints_the_local_civil_time() {
    // M4-S51/G55: moment of D at 14 and 30 is 14:30:00 on date D in the
    // local zone. The civil time is literal; the offset belongs to the
    // machine's zone, so only the civil part is asserted.
    let (out, code) = run("\
Changeable m is moment of date 2026 and 10 and 31 at 14 and 30.
Say m.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    assert!(t.starts_with("2026-10-31T14:30:00"), "got: {t}");
}

#[test]
fn m47_moment_hour_range_is_t0620() {
    // M4-S51 (the hour and minute reuse the impossible-date code - logged).
    let (out, ok) = check_source(
        "\
Changeable m is moment of today at 25 and 0.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0620"), "expected T0620, got: {out}");
}

#[test]
fn m47_in_zone_prints_that_zone_civil_time() {
    // M4-S51/G55: M in zone asia dhaka converts. Dhaka and UTC hold
    // fixed offsets (+06:00 and +00:00), so both prints are exact.
    let (out, code) = run("\
Changeable m is moment of date 2026 and 10 and 31 at 14 and 30 in zone asia dhaka.
Say m.
Changeable u is moment of date 2026 and 10 and 31 at 14 and 30 in zone utc.
Say u.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    let lines: Vec<&str> = t.lines().collect();
    assert_eq!(lines[0], "2026-10-31T14:30:00+06:00", "got: {out}");
    assert_eq!(lines[1], "2026-10-31T08:30:00+00:00", "got: {out}");
}

#[test]
fn m47_unknown_zone_is_t0171() {
    // M4-S51/T0171: a zone name no IANA zone matches is refused at
    // compile time.
    let (out, ok) = check_source(
        "\
Changeable m is now in zone nope land.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0171"), "expected T0171, got: {out}");
}

#[test]
fn m47_days_between_two_dates() {
    // M4-S52/G56: days between counts calendar days.
    let (out, code) = run("\
Say days between date 2026 and 10 and 1 and date 2026 and 10 and 31.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "30");
}

#[test]
fn m47_seconds_between_two_moments() {
    // M4-S52/G56: seconds between counts exact seconds.
    let (out, code) = run("\
Say seconds between moment of date 2026 and 10 and 31 at 12 and 30 and moment of date 2026 and 10 and 31 at 14 and 0.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "5400");
}

#[test]
fn m47_a_duration_value_prints_unit_words() {
    // M4-S52/G5: 5 seconds in a value position is a duration; the
    // print is the unit-word form (S53).
    let (out, code) = run("\
Say 5 seconds.
Say 90 seconds.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    let lines: Vec<&str> = t.lines().collect();
    assert_eq!(lines[0], "5 seconds");
    assert_eq!(lines[1], "1 minute and 30 seconds");
}

#[test]
fn m47_days_after_a_date_is_calendar() {
    // M4-S52/G56: NUMBER days after D is calendar arithmetic.
    let (out, code) = run("\
Changeable d is 2 days after date 2026 and 10 and 31.
Say d.
Changeable w is 2 weeks before date 2026 and 11 and 5.
Say w.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    let lines: Vec<&str> = t.lines().collect();
    assert_eq!(lines[0], "2026-11-02");
    assert_eq!(lines[1], "2026-10-22");
}

#[test]
fn m47_minutes_after_a_moment_keeps_the_civil_hour() {
    // M4-S52/G56: an exact-length shift on a moment moves the instant;
    // the civil time of the local zone moves with it.
    let (out, code) = run("\
Changeable m is 30 minutes after moment of date 2026 and 10 and 31 at 14 and 0.
Say m.
");
    assert_eq!(code, 0, "{out}");
    assert!(trim(&out).starts_with("2026-10-31T14:30:00"), "got: {out}");
}

#[test]
fn m47_use_seed_makes_random_reproducible() {
    // M4-S54/G57/G58: Use seed N. fixes the generator; the same seed
    // gives the same sequence in every run.
    let src = "\
Use seed 42.
Say random number from 1 to 10.
Say random number from 1 to 10.
";
    let (o1, c1) = run(src);
    let (o2, c2) = run(src);
    assert_eq!(c1, 0, "{o1}");
    assert_eq!(o1, o2, "the same seed must give the same sequence");
    let nums: Vec<i64> = trim(&o1)
        .lines()
        .map(|l| l.parse().expect("a whole number"))
        .collect();
    assert_eq!(nums.len(), 2);
    for n in nums {
        assert!((1..=10).contains(&n), "random number from 1 to 10 gave {n}");
    }
}

#[test]
fn m47_random_decimal_is_between_0_and_1() {
    // M4-S54/G57: random decimal is a decimal from 0 up to but not
    // including 1.
    let (out, code) = run("\
Use seed 42.
Say random decimal.
");
    assert_eq!(code, 0, "{out}");
    let x: f64 = trim(&out).parse().expect("a decimal");
    assert!((0.0..1.0).contains(&x), "random decimal gave {x}");
}

#[test]
fn m47_random_item_is_reproducible_with_a_seed() {
    // M4-S54/G57: one item of the collection at random.
    let src = "\
The words is list of alpha and beta and gamma and delta.
Use seed 42.
Say random item of the words.
Say random item of the words.
";
    let (o1, c1) = run(src);
    let (o2, c2) = run(src);
    assert_eq!(c1, 0, "{o1}");
    assert_eq!(o1, o2, "the same seed must give the same picks");
    let t1 = trim(&o1);
    for line in t1.lines() {
        assert!(
            ["alpha", "beta", "gamma", "delta"].contains(&line),
            "random item gave {line}"
        );
    }
}

#[test]
fn m47_shuffled_is_a_deterministic_new_list() {
    // M4-S54/G57: L shuffled is a new list in a random order; the same
    // seed gives the same order.
    let src = "\
The words is list of alpha and beta and gamma and delta.
Use seed 42.
Say the words shuffled.
";
    let (o1, c1) = run(src);
    let (o2, c2) = run(src);
    assert_eq!(c1, 0, "{o1}");
    assert_eq!(o1, o2, "the same seed must give the same order");
    // every item is still there, exactly once
    let t1 = trim(&o1);
    let mut items: Vec<&str> = t1.split(", ").flat_map(|p| p.split(" and ")).collect();
    items.sort();
    assert_eq!(items, ["alpha", "beta", "delta", "gamma"]);
}

#[test]
fn m47_hash_prints_the_sha256_hex() {
    // M4-S55/G59: hash of X is the SHA-256 of the text as 64 lower-case
    // hex digits (known vectors).
    let (out, code) = run("\
Say hash of hello.
Say hash of abc.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    let lines: Vec<&str> = t.lines().collect();
    assert_eq!(
        lines[0],
        "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
    );
    assert_eq!(
        lines[1],
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

#[test]
fn m47_secret_prints_hidden_and_reveal_gives_the_text() {
    // M4-S56/G60/G61: a secret prints hidden; reveal gives the text.
    let (out, code) = run("\
Changeable s is secret hello.
Say s.
Say reveal s.
");
    assert_eq!(code, 0, "{out}");
    let t = trim(&out);
    let lines: Vec<&str> = t.lines().collect();
    assert_eq!(lines[0], "hidden");
    assert_eq!(lines[1], "hello");
}

#[test]
fn m47_secret_of_a_non_text_is_t0113() {
    // M4-S56: secret T takes text (bytes are not values in this cut).
    let (out, ok) = check_source(
        "\
Changeable x is secret 5.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0113"), "expected T0113, got: {out}");
}

#[test]
fn m47_reveal_of_a_non_secret_is_t0113() {
    // M4-S56/G61: reveal takes a secret.
    let (out, ok) = check_source(
        "\
Changeable t is reveal hello.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0113"), "expected T0113, got: {out}");
}

#[test]
fn m47_comparing_secrets_fails_the_anonymous_way() {
    // M4-S56: secrets do not compare (a runtime refusal, anonymous).
    let (out, code) = run("\
Changeable sa is secret hello.
Changeable sb is secret hello.
If sa is sb then
    Say same.
");
    assert_ne!(code, 0, "secret comparison must fail: {out}");
    assert!(
        out.contains("The program can fail here"),
        "expected the anonymous failing-run message, got: {out}"
    );
}

#[test]
fn m47_as_text_of_a_secret_fails_the_anonymous_way() {
    // M4-S56: the only way out of a secret is reveal; as text refuses.
    let (out, code) = run("\
Changeable s is secret hello.
Say s as text.
");
    assert_ne!(code, 0, "as text of a secret must fail: {out}");
    assert!(
        out.contains("The program can fail here"),
        "expected the anonymous failing-run message, got: {out}"
    );
}

#[test]
fn m47_now_is_a_moment_value() {
    // M4-S51/G55: now is the instant in the local zone; its print is
    // the moment shape (a T separates the date and the clock).
    let (out, code) = run("Say now.\n");
    assert_eq!(code, 0, "{out}");
    assert!(trim(&out).contains('T'), "got: {out}");
}

// ===================================================================
// M4-8 (Appendix K 7.10/7.11): System - Run, Exit, signals, environment,
// Takes, Option.
// ===================================================================

/// The M4-8 tests hold this lock while they touch the process
/// environment (edition 2024 makes the writes unsafe and the env is
/// process-global; the tests run in parallel threads).
static M48_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn set_env(k: &str, v: Option<&str>) {
    // SAFETY: the caller holds M48_LOCK, so no other test thread reads
    // or writes the environment at the same time.
    unsafe {
        match v {
            Some(v) => std::env::set_var(k, v),
            None => std::env::remove_var(k),
        }
    }
}

/// The Run helper: the cargo-built helper binaries (src/bin/*_helper.rs),
/// copied under the letters-and-digits names the Run sentence accepts
/// (a Run name is one word). Real cargo binaries replaced a raw rustc
/// link, which picked stale target/debug/deps artifacts and failed with
/// E0460 once two lykaon_core builds were newer than the lykaon rlib.
fn run_helper_dir() -> std::path::PathBuf {
    static DIR: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    DIR.get_or_init(|| {
        let d = std::env::temp_dir().join(format!("lykaon_m48_helper_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).expect("helper folder");
        for (built, name) in [
            (env!("CARGO_BIN_EXE_m48sayhi_helper"), "m48sayhi.exe"),
            (env!("CARGO_BIN_EXE_m48sig_helper"), "m48sig.exe"),
        ] {
            std::fs::copy(built, d.join(name)).expect("helper copy");
        }
        d
    })
    .clone()
}

#[test]
fn m48_run_runs_a_program_on_the_path() {
    // M4-G20/S76/D16: the program is found on the path, one argument
    // per operand (its Say-display text), no shell; the child's
    // standard output is it.
    let dir = run_helper_dir();
    let _g = M48_LOCK.lock().unwrap();
    let old = std::env::var("PATH").unwrap_or_default();
    set_env("PATH", Some(&format!("{};{}", dir.display(), old)));
    let (out, code) = run("\
first is alpha.
second is beta.
Run m48sayhi with first and second.
Say it.
");
    // a missing program fails the run the anonymous way (M4-S76)
    let (out2, code2) = run("Run nosuchprog48xyz.\n");
    set_env("PATH", Some(&old));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "helper alpha beta");
    assert_ne!(code2, 0, "{out2}");
    assert!(
        out2.contains("The program can fail here"),
        "expected the anonymous failing-run message, got: {out2}"
    );
}

#[test]
fn m48_run_name_rules() {
    // T0171's row: the name carries no path (S76: the program is found
    // on the path). The path characters cannot be written (the lexer
    // refuses them, T0010), so the gate is tested directly - logged.
    assert!(lykaon::args::valid_prog_name("m48sayhi"));
    assert!(!lykaon::args::valid_prog_name("a/b"));
    assert!(!lykaon::args::valid_prog_name("a\\b"));
    assert!(!lykaon::args::valid_prog_name("c:d"));
    // a dotted spelling is refused, not truncated: the name is one word
    let (out, ok) = check_source("Run m48sayhi.exe.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
    assert!(out.contains("one word"), "{out}");
    // a symbol inside the name stops the tokens early; the sentence is
    // refused, not read as a shorter name
    let (out, ok) = check_source("Run m48_helper.bat.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
}

#[test]
fn m48_exit_ends_the_run_with_the_code() {
    // M4-S77/S78: the drops unwind, then the process ends with the
    // code; the words printed before stay printed.
    let (out, code) = run("Say before.\nExit with 3.\nSay after.\n");
    assert_eq!(code, 3, "{out}");
    assert_eq!(trim(&out), "before");
}

#[test]
fn m48_exit_zero_is_a_normal_end() {
    let (out, code) = run("Say done.\nExit with 0.\n");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "done");
}

#[test]
fn m48_exit_code_is_0_to_255() {
    // M4-S78: the code range is a compile check (T0113, the Use workers
    // precedent).
    let (out, ok) = check_source("Exit with 256.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
    let (out, ok) = check_source("Exit with 255.\n", "program.lykaon");
    assert!(ok, "{out}");
    let (out, ok) = check_source("Exit with 0.\n", "program.lykaon");
    assert!(ok, "{out}");
}

#[test]
fn m48_environment_read_gives_maybe_text() {
    // M4-G24/S80: the variable named by the words in upper case joined
    // by _; the value is maybe text.
    let _g = M48_LOCK.lock().unwrap();
    set_env("Lykaon_TEST_MODE", Some("fast"));
    let (out, code) = run("Say Environment lykaon test mode.\n");
    set_env("Lykaon_TEST_MODE", None);
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "fast");
}

#[test]
fn m48_environment_missing_reads_as_missing() {
    let _g = M48_LOCK.lock().unwrap();
    set_env("Lykaon_TEST_MODE", None);
    let (out, code) = run("Say Environment lykaon test mode.\n");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "missing");
}

#[test]
fn m48_environment_bad_name_is_refused() {
    // M4-S80: the name words spell the variable (letters, digits, _,
    // starting with a letter). In a Say the words stay text (the flat
    // rule), so the refusal shape is a value position.
    let (out, ok) = check_source("Set x to Environment 3 tries.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
}

#[test]
fn m48_read_input_gives_all_of_stdin() {
    // M4-S85: all of standard input as text (the runners read it once;
    // the buffered cut is logged).
    let (out, code) = run_source("Say Read input.\n", "program.lykaon", "cat\nsat\n");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "cat\nsat");
}

#[test]
fn m48_for_each_line_in_input() {
    // M4-G27: the lines of standard input, each without its ending;
    // the line is named line and is also it.
    let (out, code) = run_source(
        "\
For each line in input.
    Say line.
",
        "program.lykaon",
        "alpha\nbeta\n",
    );
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "alpha\nbeta");
}

#[test]
fn m48_for_each_line_empty_input_no_rounds() {
    let (out, code) = run_source(
        "\
For each line in input.
    Say line.
Say done.
",
        "program.lykaon",
        "",
    );
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "done");
}

/// The signal helper: a tiny exe (compiled with rustc next to the Run
/// helper) that fires a signal flag and then runs a source file in its
/// own process. The flags live in the helper's process, so a pending
/// flag can never leak into the test process's other runs.
fn signal_run(dir: &std::path::Path, sig: &str, src: &std::path::Path) -> (String, i32) {
    let out = std::process::Command::new(dir.join("m48sig.exe"))
        .arg("pre")
        .arg(sig)
        .arg(src)
        .output()
        .expect("m48sig helper");
    (
        String::from_utf8_lossy(&out.stdout).to_string(),
        out.status.code().unwrap_or(1),
    )
}

#[test]
fn m48_signal_without_handler_ends_with_its_code() {
    // M4-S79: a signal with no block ends the program after cleaning
    // up; the codes are 128 + the signal number (the spec lists stop
    // and interrupt's codes reversed - logged). The words printed
    // before the arrival stay printed (the poll sits after each
    // sentence).
    let dir = run_helper_dir();
    let src = dir.join("sigsrc48.lykaon");
    std::fs::write(&src, "Say before.\nSay after.\n").expect("sig source");
    for (name, want) in [("interrupt", 130), ("stop", 143), ("hangup", 129)] {
        let (out, code) = signal_run(&dir, name, &src);
        assert_eq!(code, want, "{name}: {out}");
        assert_eq!(trim(&out), "before", "{name}");
    }
}

#[test]
fn m48_signal_block_runs_and_the_run_continues() {
    // M4-S79: the block registered by the When sentence answers an
    // arrival at the next boundary, then the run continues (logged:
    // the block runs inline in its own scope). The flag arrives before
    // the run; the When registers at its sentence, and the boundary
    // right after it runs the block.
    let dir = run_helper_dir();
    let src = dir.join("sighand48.lykaon");
    std::fs::write(
        &src,
        "\
When signal interrupt arrives.
    Say handled.
Say one.
Say two.
",
    )
    .expect("sig source");
    let (out, code) = signal_run(&dir, "interrupt", &src);
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "handled\none\ntwo");
}

#[test]
fn m48_when_signal_unknown_name_refused() {
    let (out, ok) = check_source(
        "\
When signal banana arrives.
    Say no.
",
        "program.lykaon",
    );
    assert!(!ok, "{out}");
}

#[test]
fn m48_takes_seed_and_option_default() {
    // M4-G25/G26/S82: the values seed the main scope in program order;
    // a take by position, an option by flag or its default.
    let (out, code) = run_source_tool(
        "\
Takes file name as text.
Option log level is text defaulting to debug.
Say file name.
Say log level.
",
        "tool48.lykaon",
        "",
        &["report.txt".to_string()],
        true,
    );
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "report.txt\ndebug");
}

#[test]
fn m48_option_flag_value_and_bare_flag() {
    // a flag with a value, and a bare flag (a number kind reads 1, a
    // text kind reads on - logged).
    let (out, code) = run_source_tool(
        "\
Takes file name as text.
Option verbose is whole number.
Option quiet is text.
Say verbose.
Say quiet.
",
        "tool48.lykaon",
        "",
        &[
            "report.txt".to_string(),
            "--verbose".to_string(),
            "--quiet".to_string(),
        ],
        true,
    );
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "1\non");
}

#[test]
fn m48_help_gives_usage_and_exit_0() {
    // M4-S84: help or --help as the first argument prints the usage
    // text (the file stem names the tool) and exits with 0.
    let (out, code) = run_source_tool(
        "\
Takes file name as text.
Option log level is text defaulting to debug.
",
        "usage48.lykaon",
        "",
        &["--help".to_string()],
        true,
    );
    assert_eq!(code, 0, "{out}");
    assert!(out.starts_with("usage: usage48\n"), "{out}");
    assert!(out.contains("file name as text, required"), "{out}");
    assert!(
        out.contains("--log-level as text, defaulting to debug"),
        "{out}"
    );
}

#[test]
fn m48_bad_usage_gives_usage_and_exit_2() {
    // M4-S83: a missing argument, an unknown option or a value of the
    // wrong kind gives the usage text and exit 2.
    let src = "\
Takes file name as text.
Option verbose is whole number.
";
    let (out, code) = run_source_tool(src, "usage48.lykaon", "", &[], true);
    assert_eq!(code, 2, "{out}");
    assert!(out.starts_with("usage: usage48\n"), "{out}");
    let (out, code) = run_source_tool(
        src,
        "usage48.lykaon",
        "",
        &["a.txt".to_string(), "--nonsense".to_string()],
        true,
    );
    assert_eq!(code, 2, "{out}");
    let (out, code) = run_source_tool(
        src,
        "usage48.lykaon",
        "",
        &[
            "a.txt".to_string(),
            "--verbose".to_string(),
            "abc".to_string(),
        ],
        true,
    );
    assert_eq!(code, 2, "{out}");
}

#[test]
fn m48_ask_without_person_fails() {
    // M4-S86: standard input is not a terminal - Ask fails with
    // "no person here", even when stdin holds piped text.
    let (out, code) = run_source_tool(
        "\
Ask the name.
Say the name.
",
        "program.lykaon",
        "junk",
        &[],
        false,
    );
    assert_eq!(code, 1, "{out}");
    assert_eq!(trim(&out), "Error: no person here.");
}

#[test]
fn m48_program_without_takes_ignores_argv() {
    // logged: a program with no Takes and no Option declaration takes
    // no command line; its arguments are ignored (the differential
    // runs pass none either way).
    let (out, code) = run_source_tool(
        "Say hi.\n",
        "program.lykaon",
        "",
        &["whatever".to_string(), "--flag".to_string()],
        true,
    );
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "hi");
}

#[test]
fn m48_takes_stands_before_the_program() {
    // M4-S81/T0174: the declarations stand before every other sentence
    // except Note and About.
    let (out, ok) = check_source(
        "\
Note hello.
Takes file name as text.
",
        "program.lykaon",
    );
    assert!(ok, "{out}");
    let (out, ok) = check_source(
        "\
Say hi.
Takes file name as text.
",
        "program.lykaon",
    );
    assert!(!ok, "{out}");
    assert!(out.contains("T0174"), "{out}");
}

#[test]
fn m48_system_sentences_lower_embedded() {
    // the system sentences run through the evaluator: a program with
    // one lowers Embedded (the all-or-nothing gate), never Full.
    let (_, kind, _) = lykaon::native_object("Exit with 0.\n", "program.lykaon", "debug")
        .ok()
        .expect("native_object");
    assert!(
        matches!(kind, lykaon::codegen::LowerKind::Embedded { .. }),
        "{kind:?}"
    );
    let (_, kind, _) = lykaon::native_object("Takes a as text.\nSay a.\n", "t48.lykaon", "debug")
        .ok()
        .expect("native_object");
    assert!(
        matches!(kind, lykaon::codegen::LowerKind::Embedded { .. }),
        "{kind:?}"
    );
    let (_, kind, _) = lykaon::native_object("Say hi.\n", "program.lykaon", "debug")
        .ok()
        .expect("native_object");
    assert!(
        matches!(kind, lykaon::codegen::LowerKind::Full { .. }),
        "{kind:?}"
    );
}

// ---- M4-9 (Appendix K 7.12): logging and settings ----

#[test]
fn m49_log_writes_level_and_text() {
    // M4-S87/D11: Log info server started. writes "info server started"
    // and a line feed to standard error; the harnesses capture both
    // streams as one, in order (M4-D12), so the line sits in the merged
    // text exactly where the sentence ran.
    let (out, code) = run("\
Log info server started.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "info server started");
}

#[test]
fn m49_default_level_drops_debug() {
    // M4-S88: the default level is info - debug lines are not written.
    let (out, code) = run("\
Log debug quiet line.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "done");
}

#[test]
fn m49_use_log_level_debug_shows_debug_lines() {
    // M4-S88: Use log level debug. changes the level.
    let (out, code) = run("\
Use log level debug.
Log debug quiet line.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "debug quiet line\ndone");
}

#[test]
fn m49_level_order_gates_the_lines() {
    // M4-S88: the order is debug < info < warning < error. A warning
    // line shows at the default info; at warning, an info line is
    // dropped; at error, a warning line is dropped.
    let (out, code) = run("\
Log warning hot.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert!(trim(&out).contains("warning hot"), "{out}");
    let (out, code) = run("\
Use log level warning.
Log info cool.
Log warning hot.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "warning hot\ndone");
    let (out, code) = run("\
Use log level error.
Log warning hot.
Log error broke.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "error broke\ndone");
}

#[test]
fn m49_log_unknown_level_refused() {
    // the level word is one of debug, info, warning, error (S87/S88);
    // anything else cannot be read (T0113).
    let (out, ok) = check_source("Log verbose hi.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
    let (out, ok) = check_source("Log hi.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
}

#[test]
fn m49_use_log_level_unknown_word_refused() {
    let (out, ok) = check_source("Use log level loud.\n", "program.lykaon");
    assert!(!ok, "{out}");
    assert!(out.contains("T0113"), "{out}");
}

#[test]
fn m49_log_names_replaced_as_in_say() {
    // M4-S87: the text is raw text; names in it are replaced as in Say.
    let (out, code) = run("\
Changeable hits is 5.
Log info hits arrived.
Say done.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "info 5 arrived\ndone");
}

#[test]
fn m49_log_counter_shows_its_value() {
    // M4-S90: a counter is shown by the std helper Log info Hits. - the
    // counter starts at 0, Add adds, the log line shows the value.
    let (out, code) = run("\
Hits is counter.
Add 3 to hits.
Log info Hits.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "info 3");
}

#[test]
fn m49_log_secret_writes_hidden() {
    // M4-S89: a secret in a log line is written as hidden.
    let (out, code) = run("\
Changeable s is secret hunter2.
Log info the secret is s today.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "info the secret is hidden today");
}

#[test]
fn m49_log_and_say_one_stream_in_order() {
    // M4-D12: both streams are captured as one, in order - the Log line
    // sits between the Say lines in the merged text.
    let (out, code) = run("\
Say before.
Log info mid.
Say after.
");
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "before\ninfo mid\nafter");
}

#[test]
fn m49_streams_split_back_for_real_front_ends() {
    // M4-D11: the built program and the CLI write the Log lines to
    // standard error; the ranges split the one merged stream in order.
    let (merged, ranges, code) = lykaon::run_source_tool_streams(
        "Say before.\nLog info mid.\nSay after.\n",
        "m49log.lykaon",
        "",
        &[],
        true,
    );
    assert_eq!(code, 0, "{merged}");
    let (stdout_text, stderr_text) = lykaon::interp::split_streams(&merged, &ranges);
    assert_eq!(stdout_text, "before\nafter\n");
    assert_eq!(stderr_text, "info mid\n");
}

#[test]
fn m49_log_sentences_lower_embedded() {
    // the log sentences run through the evaluator like the other M4
    // system sentences (all-or-nothing gate).
    let (_, kind, _) =
        lykaon::native_object("Log info server started.\n", "m49log.lykaon", "debug")
            .ok()
            .expect("native_object");
    assert!(
        matches!(kind, lykaon::codegen::LowerKind::Embedded { .. }),
        "{kind:?}"
    );
}

#[test]
fn m49_settings_module_every_definition_shared() {
    // M4-S91: settings.lykaon is a module with every definition shared
    // (M2-S33) - no Share sentences needed - and it is read at start-up
    // before the program body, so the first sentence sees its names.
    let dir = std::env::temp_dir().join(format!("lykaon_m49_settings_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("settings.lykaon"),
        "\
Changeable greeting is hello from settings.
To double n.
    Give back n plus n.
",
    )
    .unwrap();
    let file = dir.join("m49prog.lykaon").to_string_lossy().to_string();
    let (out, code) = run_source("Use settings.\nSay greeting.\nSay double 21.\n", &file, "");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "hello from settings\n42");
}

#[test]
fn m49_settings_module_used_before_the_body_runs() {
    // M4-S91: the settings definitions are read before the program body,
    // so even the first sentence of the body sees them (a constant from
    // settings seeds the very first Say).
    let dir = std::env::temp_dir().join(format!("lykaon_m49_settings_b_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("settings.lykaon"), "Constant limit is 9.").unwrap();
    let file = dir.join("m49prog2.lykaon").to_string_lossy().to_string();
    let (out, code) = run_source(
        "Use settings.\nIf limit is more than 5.\n    Say big.\n",
        &file,
        "",
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "big");
}

// ============================================================ M4-10 (Appendix K 5.5/7.8) network

// The server tests run a Serve program on a thread (it blocks in the
// accept loop until the test process ends) and hit it from the same
// process. Every test takes its own port from a quiet range.
fn serve_bg(src: &'static str) -> u16 {
    // a port per call, in a fixed quiet range
    use std::sync::atomic::{AtomicU16, Ordering};
    static NEXT: AtomicU16 = AtomicU16::new(23401);
    let port = NEXT.fetch_add(1, Ordering::SeqCst);
    let src = src.replace("PORT", &port.to_string());
    std::thread::spawn(move || {
        let _ = run_source(&src, "m4server.lykaon", "");
    });
    // the accept loop binds within a moment
    std::thread::sleep(std::time::Duration::from_millis(700));
    port
}

#[test]
fn m4_10_fetch_home_and_read_the_record() {
    let port = serve_bg(
        "\
Serve on port PORT.
    When someone gets home.
        Respond with hello there.
",
    );
    let (out, code) = run(&format!(
        "\
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
answer is it.
Say status of answer.
Say body of answer.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "200\nhello there");
}

#[test]
fn m4_10_fetch_a_page_and_a_404() {
    let port = serve_bg(
        "\
Page users page is users.
Serve on port PORT.
    When someone gets users page.
        Respond with users here.
",
    );
    let (out, code) = run(&format!(
        "\
Page users page is users.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} users page.
answer is it.
Say body of answer.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} path nowhere.
answer2 is it.
Say status of answer2.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "users here\n404");
}

// ---- M4-10 runtime: the client and the server sides together ----

#[test]
fn m4_10_post_the_text_back() {
    // Post DATA to ADDRESS (G70): the body arrives as text of request.
    let port = serve_bg(
        "\
Serve on port PORT.
    When someone posts home.
        Respond with text of request.
",
    );
    let (out, code) = run(&format!(
        "\
Post hello to plain 127 dot 0 dot 0 dot 1 on port {port} home.
Say body of it.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "hello");
}

#[test]
fn m4_10_query_and_header_reads() {
    // with query NAME VALUE / with header NAME VALUE (G77) ride on the
    // request; the handler reads them as query NAME of request and
    // header NAME of request.
    let port = serve_bg(
        "\
Page token page is token.
Serve on port PORT.
    When someone gets home.
        Respond with query name of request.
    When someone gets token page.
        Respond with header authorization of request.
",
    );
    let (out, code) = run(&format!(
        "\
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home with query name sarah.
answer is it.
Say body of answer.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} path token with header authorization secret.
answer2 is it.
Say body of answer2.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "sarah\nsecret");
}

#[test]
fn m4_10_request_rows_method_page_parameter() {
    // The request rows (7.8): method, page and the matched parameter
    // values (anything called NAME).
    let port = serve_bg(
        "\
Page user page is user and anything called id.
Page token page is token.
Serve on port PORT.
    When someone gets user page.
        Respond with parameter id of request.
    When someone gets token page.
        Respond with page of request.
    When someone gets home.
        Respond with method of request.
",
    );
    let (out, code) = run(&format!(
        "\
Page token page is token.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} path user and 42.
Say body of it.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} token page.
Say body of it.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
Say body of it.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "42\ntoken page\nget");
}

#[test]
fn m4_10_json_respond() {
    // Respond with json X (G76/S69): the body is the json of X.
    let port = serve_bg(
        "\
Serve on port PORT.
    When someone gets home.
        Respond with json list of 1 and 2.
",
    );
    let (out, code) = run(&format!(
        "\
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
Say body of it.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "[1,2]");
}

#[test]
fn m4_10_status_codes() {
    // Respond with status N and TEXT / Respond with status N (G76).
    let port = serve_bg(
        "\
Page lost page is lost.
Serve on port PORT.
    When someone gets home.
        Respond with status 404 and gone away.
    When someone gets lost page.
        Respond with status 204.
",
    );
    let (out, code) = run(&format!(
        "\
Page lost page is lost.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
answer is it.
Say status of answer.
Say body of answer.
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} lost page.
answer2 is it.
Say status of answer2.
Say body of answer2.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "404\ngone away\n204");
}

#[test]
fn m4_10_template_fill() {
    // Respond with template NAME (S69): NAME.template from the source
    // folder, {name} filled with the visible name's value.
    let dir = std::env::temp_dir().join(format!("lykaon_m410_tmpl_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("hello.template"), "Hello {who}.").unwrap();
    let file = dir.join("m410srv.lykaon");
    let file_s = file.to_string_lossy().to_string();
    use std::sync::atomic::{AtomicU16, Ordering};
    static NEXT_T: AtomicU16 = AtomicU16::new(23481);
    let port = NEXT_T.fetch_add(1, Ordering::SeqCst);
    let src = format!(
        "\
who is sarah.
Serve on port {port}.
    When someone gets home.
        Respond with template hello.
"
    );
    std::thread::spawn(move || {
        let _ = run_source(&src, &file_s, "");
    });
    std::thread::sleep(std::time::Duration::from_millis(700));
    let (out, code) = run(&format!(
        "\
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
Say body of it.
"
    ));
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "Hello sarah.");
}

#[test]
fn m4_10_failing_handler_gives_500() {
    // A handler that fails before its Respond gives status 500 (S69).
    let port = serve_bg(
        "\
Serve on port PORT.
    When someone gets home.
        Read file mghost410 in temporary folder.
        Respond with never.
",
    );
    let (out, code) = run(&format!(
        "\
Fetch plain 127 dot 0 dot 0 dot 1 on port {port} home.
Say status of it.
"
    ));
    assert_eq!(code, 0, "{out}");
    assert_eq!(trim(&out), "500");
}

#[test]
fn m4_10_port_in_use_is_t0618() {
    // A Serve that cannot bind fails with T0618 (the code-in-the-message
    // t polish: this used to be anonymous). The listener must hold the very
    // address the server binds (Windows lets 0.0.0.0:p pass while
    // 127.0.0.1:p is held).
    let _l = std::net::TcpListener::bind(("0.0.0.0", 23511)).unwrap();
    let (out, code) = run("\
Serve on port 23511.
    When someone gets home.
        Respond with hi.
");
    assert_ne!(code, 0, "{out}");
    assert!(out.contains("T0618"), "expected T0618, got: {out}");
    assert!(
        out.contains("Serve cannot listen."),
        "expected the book's cause, got: {out}"
    );
}

// ---- M4-10 runtime: the raw sides a Lykaon program cannot spell
// (hyphenated header keys and values are unreachable in program text) ----

/// Read one WebSocket frame from the server side (unmasked, short).
fn read_ws_text(s: &mut std::net::TcpStream) -> String {
    use std::io::Read;
    let mut h = [0u8; 2];
    s.read_exact(&mut h).unwrap();
    assert_eq!(h[0] & 0x80, 0x80, "expected a finished frame");
    let len = (h[1] & 0x7F) as usize;
    assert_eq!(h[1] & 0x80, 0, "server frames are not masked");
    let mut payload = vec![0u8; len];
    s.read_exact(&mut payload).unwrap();
    String::from_utf8(payload).unwrap()
}

#[test]
fn m4_10_sessions_persist_raw_client() {
    // S72: the session map is kept in server memory under the
    // lykaon_session cookie; a client that sends the cookie back sees
    // the same session. A Lykaon program cannot spell the cookie
    // header (hyphens), so the client side is a raw HTTP client.
    let port = serve_bg(
        "\
Page name page is name.
Serve on port PORT.
    When someone gets home.
        Put hello in session under name.
        Respond with put done.
    When someone gets name page.
        Respond with value of name in session.
",
    );
    use std::io::{Read, Write};
    // first request: a new session rides home in Set-Cookie
    let mut s = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
    s.write_all(b"GET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n")
        .unwrap();
    let mut buf = String::new();
    let _ = s.read_to_string(&mut buf);
    assert!(buf.contains("200"), "{buf}");
    assert!(buf.contains("lykaon_session="), "no session cookie: {buf}");
    let cookie_value = buf
        .lines()
        .find(|l| l.to_ascii_lowercase().starts_with("set-cookie:"))
        .unwrap()
        .split_once("lykaon_session=")
        .unwrap()
        .1
        .split(';')
        .next()
        .unwrap()
        .trim()
        .to_string();
    // second request with the cookie back: the same session
    let mut s2 = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
    s2.write_all(
        format!(
            "GET /name HTTP/1.1\r\nHost: x\r\nCookie: lykaon_session={cookie_value}\r\nConnection: close\r\n\r\n"
        )
        .as_bytes(),
    )
    .unwrap();
    let mut buf2 = String::new();
    let _ = s2.read_to_string(&mut buf2);
    assert!(buf2.contains("hello"), "session lost: {buf2}");
}

#[test]
fn m4_10_websocket_echo() {
    // S73: When someone opens live chat page. upgrades the request;
    // Send x to connection. and Receive from connection. move frames.
    let port = serve_bg(
        "\
Page chat page is chat.
Serve on port PORT.
    When someone opens live chat page.
        Send welcome to connection.
        Receive from connection.
        Send it to connection.
",
    );
    use std::io::{Read, Write};
    let mut s = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
    s.write_all(
        b"GET /chat HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n",
    )
    .unwrap();
    let mut head = Vec::new();
    let mut b = [0u8; 1];
    loop {
        s.read_exact(&mut b).unwrap();
        head.push(b[0]);
        if head.ends_with(b"\r\n\r\n") {
            break;
        }
    }
    let head = String::from_utf8_lossy(&head).to_string();
    assert!(head.starts_with("HTTP/1.1 101"), "{head}");
    // the server's first frame is the welcome text
    assert_eq!(read_ws_text(&mut s), "welcome");
    // a client frame (masked with the zero mask)
    let payload = b"echo me";
    let mut f = vec![0x81u8, 0x80 | payload.len() as u8, 0, 0, 0, 0];
    f.extend_from_slice(payload);
    s.write_all(&f).unwrap();
    assert_eq!(read_ws_text(&mut s), "echo me");
}

// ---- M4-10 compile errors ----

#[test]
fn m4_10_t0521_skip_tls_outside_careful() {
    // without checking certificates is only legal inside Be careful.
    let (out, ok) = check_source(
        "Fetch plain example dot com without checking certificates.\n",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0521"), "expected T0521, got: {out}");
}

#[test]
fn m4_10_t0173_unknown_page_fetch_and_handler() {
    // a fetch place and a handler page are looked up in the Page
    // sentences (T0173).
    let (out, ok) = check_source(
        "Fetch plain example dot com ghost page.\n",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0173"), "expected T0173, got: {out}");
    let (out, ok) = check_source(
        "\
Page home page is home.
Serve on port 8080.
    When someone gets ghost page.
        Respond with hi.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0173"), "expected T0173, got: {out}");
}

#[test]
fn m4_10_t0171_address_without_host() {
    // T0170: the address needs a host; a host word also carries no
    // dot of its own (the book's Bad address code; T0171 is the Run path).
    let (out, ok) = check_source("Fetch on port 8080.\n", "program.lykaon");
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0170"), "expected T0170, got: {out}");
}

#[test]
fn m4_10_t0166_handler_without_respond() {
    // T0166: every handler path reaches one Respond.
    let (out, ok) = check_source(
        "\
Page home page is home.
Serve on port 8080.
    When someone gets home.
        Say done.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0166"), "expected T0166, got: {out}");
}

#[test]
fn m4_10_t0168_two_responds_in_a_handler() {
    // T0167: a path has two Respond sentences (the book's code; the old
    // build used T0168, which the catalogue gives to a task wait)
    let (out, ok) = check_source(
        "\
Page home page is home.
Serve on port 8080.
    When someone gets home.
        Respond with one.
        Respond with two.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0167"), "expected T0167, got: {out}");
}

#[test]
fn m4_10_respond_outside_handler_is_t0113() {
    let (out, ok) = check_source("Respond with hi.\n", "program.lykaon");
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0113"), "expected T0113, got: {out}");
}

#[test]
fn m4_10_when_outside_serve_is_t0113() {
    // T0165: When someone is not in a Serve block (the book's code)
    let (out, ok) = check_source(
        "\
Page home page is home.
When someone gets home.
    Respond with hi.
",
        "program.lykaon",
    );
    assert!(!ok, "expected a compile error, got: {out}");
    assert!(out.contains("T0165"), "expected T0165, got: {out}");
}

// ---- M4-11: git dependencies in the package manifest (M4-G84) --------------

/// Run the built lykaonc exe with `args` in `cwd`, return (stdout+stderr, code).
fn run_lykaon_in(cwd: &std::path::Path, args: &[&str]) -> (String, i32) {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_lykaonc-cli"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("lykaonc exe");
    (
        format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ),
        out.status.code().unwrap_or(-1),
    )
}

/// Run git with `args` in `cwd`, panic on failure.
fn git_in(cwd: &std::path::Path, args: &[&str]) {
    let out = std::process::Command::new("git")
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("git tool");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn m4_11_git_needs_update_flow() {
    let root = std::env::temp_dir().join(format!("m4_11_flow_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dep = root.join("widgettools");
    let proj = root.join("myapp");
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::create_dir_all(&proj).unwrap();
    // the dependency is a git repository holding an lykaon package
    std::fs::write(
        dep.join("Lykaon.toml"),
        "Name is widgettools.\nVersion is 0 point 1 point 0.\n",
    )
    .unwrap();
    std::fs::write(
        dep.join("helpers.lykaon"),
        "About this is the widget tools package.\n",
    )
    .unwrap();
    git_in(&dep, &["init", "--quiet"]);
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "one",
        ],
    );
    // the project needs it from git (a file:// address works offline)
    std::fs::write(
        proj.join("Lykaon.toml"),
        format!(
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds widgettools from git file://{}.\n",
            dep.display().to_string().replace('\\', "/")
        ),
    )
    .unwrap();
    let (out, code) = run_lykaon_in(&proj, &["update"]);
    assert_eq!(code, 0, "update failed: {out}");
    assert!(out.contains("Fetched widgettools from git."), "{out}");
    assert!(out.contains("Wrote lykaon.lock."), "{out}");
    // the clone landed in the cache and the lock records the git source
    assert!(
        proj.join(".lykaon-cache")
            .join("widgettools")
            .join("Lykaon.toml")
            .is_file()
    );
    let lock = std::fs::read_to_string(proj.join("lykaon.lock")).unwrap();
    assert!(
        lock.contains("Locked widgettools from git file://"),
        "{lock}"
    );
}

#[test]
fn m4_11_git_needs_pin_checkout_version() {
    let root = std::env::temp_dir().join(format!("m4_11_pin_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dep = root.join("pinned");
    let proj = root.join("myapp");
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::create_dir_all(&proj).unwrap();
    std::fs::write(
        dep.join("Lykaon.toml"),
        "Name is pinned.\nVersion is 0 point 1 point 0.\n",
    )
    .unwrap();
    std::fs::write(dep.join("helpers.lykaon"), "About version one.\n").unwrap();
    git_in(&dep, &["init", "--quiet"]);
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "one",
        ],
    );
    // the tag sits on the FIRST commit; a second commit moves the branch
    git_in(&dep, &["tag", "v0.1.0"]);
    std::fs::write(dep.join("helpers.lykaon"), "About version two.\n").unwrap();
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "two",
        ],
    );
    std::fs::write(
        proj.join("Lykaon.toml"),
        format!(
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds pinned from git file://{} at version 0 point 1 point 0.\n",
            dep.display().to_string().replace('\\', "/")
        ),
    )
    .unwrap();
    let (out, code) = run_lykaon_in(&proj, &["update"]);
    assert_eq!(code, 0, "update failed: {out}");
    // the cache is on the tagged commit, not the branch head
    let helpers = std::fs::read_to_string(
        proj.join(".lykaon-cache")
            .join("pinned")
            .join("helpers.lykaon"),
    )
    .unwrap();
    assert!(
        helpers.contains("version one"),
        "the pinned checkout is wrong: {helpers}"
    );
}

#[test]
fn m4_11_git_bad_address_gives_t0520() {
    let root = std::env::temp_dir().join(format!("m4_11_bad_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let proj = root.join("myapp");
    std::fs::create_dir_all(&proj).unwrap();
    let missing = root.join("no-such-repo");
    std::fs::write(
        proj.join("Lykaon.toml"),
        format!(
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds ghost from git file://{}.\n",
            missing.display().to_string().replace('\\', "/")
        ),
    )
    .unwrap();
    let (out, code) = run_lykaon_in(&proj, &["update"]);
    assert_ne!(code, 0, "update should fail: {out}");
    assert!(out.contains("T0520"), "{out}");
    assert!(out.contains("Git dependency failed"), "{out}");
    assert!(
        out.contains("Check the address and run lykaon update."),
        "{out}"
    );
}

#[test]
fn m4_11_lock_records_a_checksum_and_a_second_update_is_idempotent() {
    let root = std::env::temp_dir().join(format!("m4_11_sum_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dep = root.join("checked");
    let proj = root.join("myapp");
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::create_dir_all(&proj).unwrap();
    std::fs::write(
        dep.join("Lykaon.toml"),
        "Name is checked.\nVersion is 0 point 1 point 0.\n",
    )
    .unwrap();
    std::fs::write(dep.join("main.lykaon"), "About one.\n").unwrap();
    git_in(&dep, &["init", "--quiet"]);
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "one",
        ],
    );
    git_in(&dep, &["tag", "v0.1.0"]);
    std::fs::write(
        proj.join("Lykaon.toml"),
        format!(
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds checked from git file://{} at version 0 point 1 point 0.\n",
            dep.display().to_string().replace('\\', "/")
        ),
    )
    .unwrap();
    let (out, code) = run_lykaon_in(&proj, &["update"]);
    assert_eq!(code, 0, "{out}");
    let lock = std::fs::read_to_string(proj.join("lykaon.lock")).unwrap();
    assert!(
        lock.contains("with checksum "),
        "the lock has no checksum: {lock}"
    );
    let checksum_line = lock
        .lines()
        .find(|l| l.starts_with("Locked checked"))
        .unwrap()
        .to_string();
    // a second update with unchanged content succeeds and keeps the lock
    let (out2, code2) = run_lykaon_in(&proj, &["update"]);
    assert_eq!(code2, 0, "second update failed: {out2}");
    let lock2 = std::fs::read_to_string(proj.join("lykaon.lock")).unwrap();
    assert_eq!(lock, lock2, "the lock changed on an unchanged dependency");
    assert!(checksum_line.contains("with checksum "));
}

#[test]
fn m4_11_rewritten_version_tag_is_t0520_checksum_differs() {
    let root = std::env::temp_dir().join(format!("m4_11_tag_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dep = root.join("moved");
    let proj = root.join("myapp");
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::create_dir_all(&proj).unwrap();
    std::fs::write(
        dep.join("Lykaon.toml"),
        "Name is moved.\nVersion is 0 point 1 point 0.\n",
    )
    .unwrap();
    std::fs::write(dep.join("main.lykaon"), "About first content.\n").unwrap();
    git_in(&dep, &["init", "--quiet"]);
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "one",
        ],
    );
    git_in(&dep, &["tag", "v0.1.0"]);
    std::fs::write(
        proj.join("Lykaon.toml"),
        format!(
            "Name is myapp.\nVersion is 1 point 0 point 0.\nNeeds moved from git file://{} at version 0 point 1 point 0.\n",
            dep.display().to_string().replace('\\', "/")
        ),
    )
    .unwrap();
    let (out, code) = run_lykaon_in(&proj, &["update"]);
    assert_eq!(code, 0, "{out}");
    // the version tag is rewritten to new content (a rewritten release)
    std::fs::write(dep.join("main.lykaon"), "About second content.\n").unwrap();
    git_in(&dep, &["add", "."]);
    git_in(
        &dep,
        &[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "--quiet",
            "-m",
            "two",
        ],
    );
    git_in(&dep, &["tag", "-f", "v0.1.0"]);
    // update re-fetches the moved tag and refuses the changed checksum
    let (out2, code2) = run_lykaon_in(&proj, &["update"]);
    assert_ne!(code2, 0, "the rewritten tag must fail: {out2}");
    assert!(out2.contains("T0520"), "{out2}");
    assert!(out2.contains("checksum"), "{out2}");
}

#[test]
fn m4_11_add_git_url_writes_manifest() {
    let root = std::env::temp_dir().join(format!("m4_11_add_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let dep = root.join("widgettools");
    let proj = root.join("myapp");
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::create_dir_all(&proj).unwrap();
    std::fs::write(
        proj.join("Lykaon.toml"),
        "Name is myapp.\nVersion is 1 point 0 point 0.\nEntry is main.lykaon.\n",
    )
    .unwrap();
    let url = format!("file://{}", dep.display().to_string().replace('\\', "/"));
    let (out, code) = run_lykaon_in(&proj, &["add", &url]);
    assert_eq!(code, 0, "add failed: {out}");
    let toml = std::fs::read_to_string(proj.join("Lykaon.toml")).unwrap();
    assert!(
        toml.contains(&format!("Needs widgettools from git {url}.")),
        "{toml}"
    );
}

// ---- M4 tools: `lykaon build` writes a runnable program (M4-D17) ----------
//
// Before this test, `lykaon build` wrote only the object file, so the language
// could not actually make a command-line tool. The output must be a program the
// system runs, not an .obj.

#[test]
fn m4_build_writes_a_runnable_program() {
    let dir = std::env::temp_dir().join(format!("m4_build_exe_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("hello.lykaon"), "Say hello.\n").unwrap();
    let (out, code) = run_lykaon_in(&dir, &["build", "debug", "hello.lykaon"]);
    assert_eq!(code, 0, "build failed: {out}");
    let exe = dir.join(format!(
        "build/hello{}",
        if cfg!(windows) { ".exe" } else { "" }
    ));
    assert!(exe.exists(), "expected {exe:?}, got: {out}");
    let run = std::process::Command::new(&exe)
        .output()
        .expect("the built program must run");
    assert!(
        run.status.success(),
        "built program exited {:?}",
        run.status.code()
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "hello");
    // The intermediate object must not be left beside the program.
    assert!(
        !dir.join("build/hello.obj").exists() && !dir.join("build/hello.o").exists(),
        "the object file leaked into the output folder: {out}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
