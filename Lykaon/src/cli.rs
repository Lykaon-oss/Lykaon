//! The interpreter/REPL front's shared entry points (the lykaon-cli exe).
//!
//! The compiler front is the lykaonc-cli exe (src/main.rs); the interpreter
//! front is the lykaon-cli exe (src/bin/lykaon.rs). Both link this crate;
//! the run_interpreter and repl_session live here so the two fronts
//! share one implementation.

use std::io::IsTerminal;
use std::process::ExitCode;

/// The interpreter path of the run tool (M4-D17's --interpret and the
/// missing-toolchain fallback): read standard input fully (the buffer the
/// language's reads slide through), parse the program's own arguments
/// against its Takes/Option spec (M4-S82), and run with the real person
/// flag (M4-S86). The signal flags arm before the run (M4-S79).
pub fn run_interpreter(source: String, file: String, prog_args: Vec<String>) -> ExitCode {
    use std::io::Read;
    let stdin_text = {
        let mut buf = String::new();
        let _ = std::io::stdin().lock().read_to_string(&mut buf);
        buf
    };
    crate::signals::arm();
    let interactive = std::io::IsTerminal::is_terminal(&std::io::stdin());
    // The interpreter recurses per nested call; T0607 allows 240 nested
    // calls, which a 1 MB main-thread stack cannot hold in debug builds.
    // Run it on a roomy worker thread.
    let (tx, rx) = std::sync::mpsc::channel::<(String, Vec<(usize, usize)>, i32)>();
    let h = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let (out, ranges, code) = crate::run_source_tool_streams(
                &source,
                &file,
                &stdin_text,
                &prog_args,
                interactive,
            );
            let _ = tx.send((out, ranges, code));
        })
        .expect("cannot spawn the interpreter thread");
    let (merged, ranges, code) = rx.recv().unwrap_or((String::new(), Vec::new(), 101));
    let _ = h.join();
    // M4-D11 (7.12): Log lines belong to standard error. The run's output
    /// is the one merged stream; the ranges split it back, in order.
    // bad usage (M4-S83) prints on standard error; the program output and
    // --help's usage text (M4-S84) print on standard output
    if code == 2 {
        eprint!("{merged}");
    } else {
        let (stdout_text, stderr_text) = crate::interp::split_streams(&merged, &ranges);
        print!("{stdout_text}");
        eprint!("{stderr_text}");
    }
    let _ = std::io::Write::flush(&mut std::io::stdout());
    ExitCode::from(code as u8)
}

/// The REPL session (M1b): one sentence at a time; a block opener waits
/// for its indented body; quit. ends. The lykaon front's repl.
pub fn repl_session() -> ExitCode {
    use std::io::Write;
    println!("Lykaon - type one sentence and press Enter. quit. ends.");
    println!("A block opener (If ..., To ..., ...) waits for its indented body.");
    // the session's committed program: everything that ran successfully
    let mut committed = String::new();
    // what is being typed right now (committed + unfinished lines)
    let mut text = String::new();
    // how much of the last run's output was already shown (the program
    // re-runs whole, so only the new tail is printed)
    let mut printed = 0usize;
    loop {
        if text == committed {
            print!("lykaon> ");
        } else {
            print!("  ...> ");
        }
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        match std::io::stdin().read_line(&mut line) {
            Ok(0) => break, // end of input
            Ok(_) => {}
            Err(_) => break,
        }
        let t = line.trim_end();
        let trimmed = t.trim();
        if trimmed.is_empty() {
            continue;
        }
        if trimmed == "quit." || trimmed == "quit" || trimmed == "exit." || trimmed == "exit" {
            break;
        }
        let candidate = format!("{text}{}\n", t);
        // keep the prompt open while the sentence has no period yet or a
        // block opener has no indented body under it (T0014)
        let incomplete = !trimmed.ends_with('.') || {
            let (out, ok) = crate::check_source(&candidate, "repl");
            !ok && out.contains("T0014")
        };
        if incomplete {
            text = candidate;
            continue;
        }
        let (out, code) = crate::run_source(&candidate, "repl", "");
        if code == 0 {
            text = candidate.clone();
            committed = candidate;
            printed = print_new_tail(&out, printed);
        } else {
            // the new line made the program fail: show why and drop
            // everything typed since the last clean run, so one bad
            // sentence cannot poison the session
            printed = print_new_tail(&out, printed);
            text = committed.clone();
        }
        // display only: keep the next prompt on its own line (this does
        // not change what counts as already shown)
        if !out.ends_with('\n') {
            println!();
        }
        let _ = std::io::stdout().flush();
    }
    ExitCode::from(0)
}

/// Print only the part of `out` that was not shown before (the program
/// re-runs whole each time). Returns the new shown length. When the
/// prefix changed (nondeterministic output) the whole text is shown.
fn print_new_tail(out: &str, printed: usize) -> usize {
    if out.len() >= printed && (printed == 0 || out.as_bytes()[printed - 1] == b'\n') {
        // align the tail to a line start so a partial line is not split
        print!("{}", &out[printed..]);
        out.len()
    } else {
        print!("{out}");
        out.len()
    }
}
