//! The lykaon front: the interpreter/REPL.
//!
//! The compiler front is the lykaonc exe (src/main.rs). This front runs
//! the interpreter only: `lykaon run <file> [args]` (the M4-D17
//! --interpret path, the default of this front) and `lykaon repl`
//! (the REPL). The compiler commands (the native run, build, check, ...)
//! belong to lykaonc.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("run") => {
            // the lykaon flags belong before the file; everything after
            // the file is the program's own command line (M4-S82).
            // --interpret is this front's default (the flag is accepted);
            // the compiler flags belong to lykaonc
            let mut file: Option<String> = None;
            let mut prog_args: Vec<String> = Vec::new();
            let mut i = 2;
            while i < args.len() {
                let a = args[i].as_str();
                if file.is_none() {
                    match a {
                        "--interpret" => {} // this front's default
                        "--native" | "--fast" | "--small" => {
                            eprintln!("the compiler front is lykaonc-cli ({a} belongs there)");
                            return ExitCode::from(2);
                        }
                        _ => file = Some(args[i].clone()),
                    }
                } else {
                    prog_args.push(args[i].clone());
                }
                i += 1;
            }
            let Some(file) = file else {
                eprintln!("usage: lykaon-cli run <file> [arguments]");
                eprintln!("the compiler front (the native run) is lykaonc-cli run");
                return ExitCode::from(2);
            };
            let source = match std::fs::read_to_string(&file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {file}: {e}");
                    return ExitCode::from(1);
                }
            };
            lykaon::cli::run_interpreter(source, file, prog_args)
        }
        Some("repl") => lykaon::cli::repl_session(),
        Some("ui") | Some("--ui") => {
            #[cfg(feature = "gui")]
            {
                lykaon::ui::interpreter::run();
                ExitCode::from(0)
            }
            #[cfg(not(feature = "gui"))]
            {
                eprintln!(
                    "the interpreter UI is built with: cargo build --features gui --bin Lykaon"
                );
                ExitCode::from(2)
            }
        }
        Some(other) => {
            eprintln!(
                "the lykaon front runs the interpreter: lykaon run <file> | lykaon repl | lykaon ui"
            );
            eprintln!("the compiler front is lykaonc-cli ({other} belongs there)");
            ExitCode::from(2)
        }
        None => {
            eprintln!("usage: lykaon-cli run <file> [arguments] | lykaon repl | lykaon ui");
            eprintln!("the compiler front is lykaonc-cli (build, check, native run, ui)");
            ExitCode::from(2)
        }
    }
}
