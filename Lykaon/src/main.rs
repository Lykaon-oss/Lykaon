use lykaon::{NativeFail, check_source, format_source, native_run_tool, packages};
use std::io::IsTerminal;
use std::{env, path::PathBuf, process::ExitCode};

fn main() -> ExitCode {
    // a double click on the exe opens a console that would close before
    // the usage text can be read: when stdout is a real console window,
    // wait for Enter before closing (piped and automated runs are
    // unaffected - they are not terminals)
    let interactive_console = std::io::stdout().is_terminal();
    std::panic::set_hook(Box::new(move |info| {
        eprintln!("{info}");
        if std::io::stderr().is_terminal() {
            eprintln!("\nPress Enter to close...");
            let mut line = String::new();
            let _ = std::io::stdin().read_line(&mut line);
        }
    }));
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: lykaonc-cli <command> [args]");
        eprintln!("commands: run file.lykaon | check file.lykaon | fmt file.lykaon | test [file]");
        eprintln!("          build file.lykaon | repl | ui | bench | add <folder-or-url>");
        eprintln!("          remove <name> | update");
        if interactive_console {
            // a double click opens a console: write and test code right
            // here instead of closing
            return lykaon::cli::repl_session();
        }
        return ExitCode::from(2);
    }
    match args[1].as_str() {
        "check" => {
            if args.len() < 3 {
                eprintln!("usage: lykaon check <file>");
                return ExitCode::from(2);
            }
            let file = &args[2];
            // read bytes, not text: a file that is not UTF-8 is T0018
            let bytes = match std::fs::read(file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {file}: {e}");
                    return ExitCode::from(1);
                }
            };
            let (out, ok) = lykaon::check_bytes(&bytes, file);
            print!("{}", out);
            if ok {
                ExitCode::from(0)
            } else {
                ExitCode::from(1)
            }
        }
        "fmt" => {
            if args.len() < 3 {
                eprintln!("usage: lykaon fmt <file>");
                return ExitCode::from(2);
            }
            let file = &args[2];
            let source = match std::fs::read_to_string(file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {file}: {e}");
                    return ExitCode::from(1);
                }
            };
            print!("{}", format_source(&source));
            ExitCode::from(0)
        }
        "run" => {
            // M4-D17 (Appendix K 7.11): from M4 the run tool runs native by
            // default; the interpreter is the explicit --interpret choice.
            // The lykaon flags belong before the file name; everything after
            // the file is the program's own command line (M4-S82).
            let mut interpret = false;
            let mut native_mode: Option<&'static str> = None;
            let mut file: Option<String> = None;
            let mut prog_args: Vec<String> = Vec::new();
            let mut i = 2;
            while i < args.len() {
                let a = args[i].as_str();
                if file.is_none() {
                    match a {
                        "--interpret" => interpret = true,
                        "--native" => {}
                        "--fast" => native_mode = Some("fast"),
                        "--small" => native_mode = Some("small"),
                        _ => file = Some(args[i].clone()),
                    }
                } else {
                    prog_args.push(args[i].clone());
                }
                i += 1;
            }
            let Some(file) = file else {
                eprintln!(
                    "usage: lykaon run [--interpret | [--fast | --small]] <file> [arguments]"
                );
                return ExitCode::from(2);
            };
            let source = match std::fs::read_to_string(&file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {file}: {e}");
                    return ExitCode::from(1);
                }
            };
            if !interpret {
                // Native mode (M4-D17 default): compile, link with
                // liblykaon_rt, and run the built program with the program's
                // arguments (M4-S82). A missing native toolchain falls
                // back to the interpreter with a note (the differential
                // guarantee makes the two byte-identical).
                match native_run_tool(&source, &file, native_mode.unwrap_or("debug"), &prog_args) {
                    Ok((code, out, err)) => {
                        print!("{out}");
                        let _ = std::io::Write::flush(&mut std::io::stdout());
                        if !err.is_empty() {
                            eprint!("{err}");
                        }
                        ExitCode::from(code as u8)
                    }
                    Err(NativeFail::Diags(text)) => {
                        // diagnostics print to the console exactly like the
                        // interpreter's compile does (M3 differential rule)
                        print!("{text}");
                        let _ = std::io::Write::flush(&mut std::io::stdout());
                        ExitCode::from(1)
                    }
                    Err(NativeFail::Tool(e)) => {
                        eprintln!("Note: {e}");
                        eprintln!("Note: running with the interpreter instead.");
                        lykaon::cli::run_interpreter(source, file.clone(), prog_args.clone())
                    }
                }
            } else {
                lykaon::cli::run_interpreter(source, file, prog_args)
            }
        }
        "test" => {
            if args.len() < 3 {
                eprintln!("usage: lykaon test <file>");
                return ExitCode::from(2);
            }
            let file = &args[2];
            let source = match std::fs::read_to_string(file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {file}: {e}");
                    return ExitCode::from(1);
                }
            };
            let (out, ok) = lykaon::test_source(&source, file, "");
            print!("{out}");
            let _ = std::io::Write::flush(&mut std::io::stdout());
            ExitCode::from(if ok { 0 } else { 1 })
        }
        "repl" => lykaon::cli::repl_session(),
        "ui" | "--ui" => {
            #[cfg(feature = "gui")]
            {
                lykaon::ui::compiler::run();
                ExitCode::from(0)
            }
            #[cfg(not(feature = "gui"))]
            {
                eprintln!(
                    "the compiler UI is built with: cargo build --features gui --bin Lykaonc"
                );
                ExitCode::from(2)
            }
        }
        "add" => {
            if args.len() < 3 {
                eprintln!("usage: lykaon add <folder>");
                return ExitCode::from(2);
            }
            let folder = &args[2];
            let toml = PathBuf::from("Lykaon.toml");
            let text = match std::fs::read_to_string(&toml) {
                Ok(s) => s,
                Err(_) => {
                    eprintln!("Error: no Lykaon.toml here. Create one first.");
                    return ExitCode::from(1);
                }
            };
            let mut proj = match packages::parse_project(&text) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(1);
                }
            };
            if proj.needs.iter().any(|d| d.name == *folder) {
                eprintln!("Error: {folder} is already a dependency.");
                return ExitCode::from(1);
            }
            if packages::looks_like_git_url(folder) {
                let name = packages::name_from_git_url(folder);
                if proj.needs.iter().any(|d| d.name == name) {
                    eprintln!("Error: {name} is already a dependency.");
                    return ExitCode::from(1);
                }
                proj.needs.push(packages::Dependency {
                    name,
                    source: packages::Source::Git {
                        url: folder.clone(),
                        version: None,
                    },
                });
            } else {
                proj.needs.push(packages::Dependency {
                    name: folder.clone(),
                    source: packages::Source::Folder(PathBuf::from(folder)),
                });
            }
            let mut out = String::new();
            if let Some(n) = &proj.name {
                out.push_str(&format!("Name is {n}.\n"));
            }
            if let Some((ma, mi, pa)) = proj.version {
                out.push_str(&format!("Version is {ma} point {mi} point {pa}.\n"));
            }
            if let Some(e) = &proj.entry {
                out.push_str(&format!("Entry is {e}.\n"));
            }
            for dep in &proj.needs {
                match &dep.source {
                    packages::Source::Folder(f) => {
                        out.push_str(&format!(
                            "Needs {} from folder {}.\n",
                            dep.name,
                            f.display()
                        ));
                    }
                    packages::Source::Git { url, version } => match version {
                        Some((ma, mi, pa)) => out.push_str(&format!(
                            "Needs {} from git {} at version {ma} point {mi} point {pa}.\n",
                            dep.name, url
                        )),
                        None => out.push_str(&format!("Needs {} from git {}.\n", dep.name, url)),
                    },
                }
            }
            match std::fs::write(&toml, &out) {
                Ok(()) => {
                    println!("Added dependency {folder}. Run lykaon update to write lykaon.lock.");
                    ExitCode::from(0)
                }
                Err(e) => {
                    eprintln!("Error: cannot write Lykaon.toml: {e}");
                    ExitCode::from(1)
                }
            }
        }
        "remove" => {
            if args.len() < 3 {
                eprintln!("usage: lykaon remove <name>");
                return ExitCode::from(2);
            }
            let name = &args[2];
            let toml = PathBuf::from("Lykaon.toml");
            let text = match std::fs::read_to_string(&toml) {
                Ok(s) => s,
                Err(_) => {
                    eprintln!("Error: no Lykaon.toml here. Create one first.");
                    return ExitCode::from(1);
                }
            };
            let mut proj = match packages::parse_project(&text) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(1);
                }
            };
            let before = proj.needs.len();
            proj.needs.retain(|d| d.name != *name);
            if proj.needs.len() == before {
                eprintln!("Error: {name} is not a dependency.");
                return ExitCode::from(1);
            }
            let mut out = String::new();
            if let Some(n) = &proj.name {
                out.push_str(&format!("Name is {n}.\n"));
            }
            if let Some((ma, mi, pa)) = proj.version {
                out.push_str(&format!("Version is {ma} point {mi} point {pa}.\n"));
            }
            if let Some(e) = &proj.entry {
                out.push_str(&format!("Entry is {e}.\n"));
            }
            for dep in &proj.needs {
                match &dep.source {
                    packages::Source::Folder(f) => {
                        out.push_str(&format!(
                            "Needs {} from folder {}.\n",
                            dep.name,
                            f.display()
                        ));
                    }
                    packages::Source::Git { url, version } => match version {
                        Some((ma, mi, pa)) => out.push_str(&format!(
                            "Needs {} from git {} at version {ma} point {mi} point {pa}.\n",
                            dep.name, url
                        )),
                        None => out.push_str(&format!("Needs {} from git {}.\n", dep.name, url)),
                    },
                }
            }
            match std::fs::write(&toml, &out) {
                Ok(()) => {
                    println!("Removed dependency {name}.");
                    ExitCode::from(0)
                }
                Err(e) => {
                    eprintln!("Error: cannot write Lykaon.toml: {e}");
                    ExitCode::from(1)
                }
            }
        }
        "update" => {
            let toml = PathBuf::from("Lykaon.toml");
            let text = match std::fs::read_to_string(&toml) {
                Ok(s) => s,
                Err(_) => {
                    eprintln!("Error: no Lykaon.toml here. Create one first.");
                    return ExitCode::from(1);
                }
            };
            let proj = match packages::parse_project(&text) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(1);
                }
            };
            // the previous lock lets `lykaon update` catch a rewritten tag
            // (T0520's "its checksum differs"); a damaged lock is T0516
            let old_lock = match std::fs::read_to_string("lykaon.lock") {
                Ok(t) => match packages::parse_lockfile(&t) {
                    Ok(l) => Some(l),
                    Err(e) => {
                        eprintln!("{e}");
                        return ExitCode::from(1);
                    }
                },
                Err(_) => None,
            };
            // git dependencies are fetched into the cache first (M4-11);
            // a failure is T0520 with the book's fix wording
            let fetched = match packages::sync_git_deps(
                &proj,
                &std::env::current_dir().unwrap_or_default(),
                old_lock.as_ref(),
            ) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(1);
                }
            };
            for (name, _) in &fetched {
                println!("Fetched {name} from git.");
            }
            if let Err(e) =
                packages::validate_deps(&proj, &std::env::current_dir().unwrap_or_default())
            {
                eprintln!("{e}");
                return ExitCode::from(1);
            }
            let lock = packages::write_lockfile(&proj, &fetched);
            match std::fs::write("lykaon.lock", &lock) {
                Ok(()) => {
                    println!("Wrote lykaon.lock.");
                    ExitCode::from(0)
                }
                Err(e) => {
                    eprintln!("Error: cannot write lykaon.lock: {e}");
                    ExitCode::from(1)
                }
            }
        }
        "build" => {
            // M3-S44: `lykaon build <debug|fast|small> [input.lykaon] [output]`,
            // the default output being build/<stem>.obj; the summary line is
            // `built <stem> in <mode>`, with the lowering reported honestly.
            let mode = if args.len() >= 3 {
                args[2].as_str()
            } else {
                "debug"
            };
            let input_file = if args.len() >= 4 {
                args[3].as_str()
            } else {
                "main.lykaon"
            };
            if !matches!(mode, "debug" | "fast" | "small") {
                eprintln!("usage: lykaon build <debug|fast|small> [input.lykaon] [output]");
                return ExitCode::from(2);
            }
            let output_file = if args.len() >= 5 {
                args[4].clone()
            } else {
                let stem = std::path::Path::new(input_file)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("program");
                // `lykaon build` produces a runnable program, not an object:
                // the .lykaon source becomes a native executable (the M4
                // requirement that the language makes command-line tools).
                format!("build/{stem}{}", lykaon::linker::exe_suffix())
            };
            // An output named .obj/.o explicitly asks for the object only, the
            // M3 behaviour the bench and differential harnesses rely on.
            let object_only = matches!(
                std::path::Path::new(&output_file)
                    .extension()
                    .and_then(|e| e.to_str()),
                Some("obj") | Some("o")
            );
            let source = match std::fs::read_to_string(input_file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error: cannot read {input_file}: {e}");
                    return ExitCode::from(1);
                }
            };
            let _ = std::fs::create_dir_all(
                std::path::Path::new(&output_file)
                    .parent()
                    .unwrap_or(std::path::Path::new(".")),
            );
            match lykaon::native_object(&source, input_file, mode) {
                Ok((obj_bytes, kind, reports)) => {
                    let stem = std::path::Path::new(input_file)
                        .file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or("program");
                    // Write the object beside the final program, then link.
                    // An object-only request writes straight to output_file.
                    let obj_path = if object_only {
                        std::path::PathBuf::from(&output_file)
                    } else {
                        std::path::PathBuf::from(format!(
                            "{}.lykaon-obj-{}{}",
                            output_file,
                            std::process::id(),
                            if cfg!(windows) { ".obj" } else { ".o" }
                        ))
                    };
                    if let Err(e) = std::fs::write(&obj_path, &obj_bytes) {
                        eprintln!("Error: cannot write {}: {e}", obj_path.display());
                        return ExitCode::from(1);
                    }
                    if !object_only {
                        let linked = lykaon::linker::find_rt_lib()
                            .map_err(|e| format!("the runtime library is missing: {e}"))
                            .and_then(|rt| {
                                lykaon::linker::link_exe(
                                    &obj_path,
                                    &rt,
                                    std::path::Path::new(&output_file),
                                )
                            });
                        let _ = std::fs::remove_file(&obj_path);
                        if let Err(e) = linked {
                            eprintln!("Error: {e}");
                            return ExitCode::from(1);
                        }
                    }
                    println!("built {stem} in {mode}");
                    match kind {
                        lykaon::codegen::LowerKind::Full => {
                            println!("{output_file} — machine code (full scalar lowering)")
                        }
                        lykaon::codegen::LowerKind::Embedded { reason } => {
                            println!("{output_file} — embedded evaluator: {reason}")
                        }
                    }
                    for r in &reports {
                        println!(
                            "  optimizer: {} — {} change{}",
                            r.name,
                            r.changes,
                            if r.changes == 1 { "" } else { "s" }
                        );
                    }
                    ExitCode::from(0)
                }
                Err(f) => {
                    // diagnostics print to the console like the interpreter's
                    print!("{}", f.message());
                    let _ = std::io::Write::flush(&mut std::io::stdout());
                    ExitCode::from(1)
                }
            }
        }
        "bench" => {
            let bench_dir = PathBuf::from("tests/bench");
            if !bench_dir.is_dir() {
                eprintln!("Error: tests/bench/ not found.");
                return ExitCode::from(1);
            }
            let rust_ref_path = bench_dir.join("rust_reference.json");
            let rust_times: Vec<(String, f64)> = match std::fs::read_to_string(&rust_ref_path) {
                Ok(text) => serde_json::from_str::<Vec<(String, f64)>>(&text).unwrap_or_else(|e| {
                    eprintln!("Error: cannot parse {}: {e}", rust_ref_path.display());
                    std::process::exit(1);
                }),
                Err(_) => {
                    eprintln!(
                        "Error: cannot read {}. Build the Rust reference benchmarks first.",
                        rust_ref_path.display()
                    );
                    return ExitCode::from(1);
                }
            };
            let rust_ref_dir = bench_dir.join("reference").join("bin");
            let bench_exe_dir = bench_dir.join("bin");
            let _ = std::fs::create_dir_all(&bench_exe_dir);

            // Stored reference times are a staleness cross-check only; the
            // P-061 ratios are computed from Rust medians measured in this
            // run (see below), so both sides are same-method, same-run.
            let mut rat_d: Vec<f64> = Vec::new();
            let mut rat_f: Vec<f64> = Vec::new();
            // M3b-6: contract checks the prover proves skippable, summed
            // over every benchmark program (Ensures contracts + Always sites).
            let mut checks_total: usize = 0;
            for (name, rust_ms) in &rust_times {
                let lykaon_path = bench_dir.join(format!("{name}.lykaon"));
                let source = match std::fs::read_to_string(&lykaon_path) {
                    Ok(s) => s,
                    Err(_) => {
                        eprintln!(
                            "Error: cannot read {lykaon_path:?}. Write the benchmark program first."
                        );
                        return ExitCode::from(1);
                    }
                };
                let rust_exe = rust_ref_dir.join(format!("{name}.exe"));
                if !rust_exe.is_file() {
                    eprintln!("Error: Rust reference exe not found: {rust_exe:?}. Build it first.");
                    return ExitCode::from(1);
                }

                // M3b-6: count how many contract checks the prover removes
                // for this benchmark program (the interpreter/net check
                // count is mode-independent, so one pass is enough).
                let checks = match lykaon::compile_tree(&source, lykaon_path.to_str().unwrap()) {
                    Ok(mut p) => lykaon::prover::checks_removed(&mut p),
                    Err(ds) => {
                        eprintln!(
                            "Error: {name} does not compile for prover counting: {} diagnostic(s)",
                            ds.len()
                        );
                        return ExitCode::from(1);
                    }
                };
                checks_total += checks;

                // Lykaon default (debug): compile once (timed), then run 10x.
                let (lykaon_exe_d, compile_ms_d) = match lykaon::native_compile_to_exe(
                    &source,
                    lykaon_path.to_str().unwrap(),
                    "debug",
                    &bench_exe_dir,
                ) {
                    Ok(r) => r,
                    Err(e) => {
                        eprintln!(
                            "Error: {name} lykaon compile (debug) failed: {}",
                            e.message()
                        );
                        return ExitCode::from(1);
                    }
                };
                let _ = lykaon::run_exe(&lykaon_exe_d); // warm up
                let mut times_d: Vec<f64> = Vec::new();
                let mut out_d = String::new();
                for _ in 0..10 {
                    match lykaon::run_exe(&lykaon_exe_d) {
                        Ok((code, out, ms)) => {
                            if code != 0 {
                                eprintln!(
                                    "Error: {name} lykaon run (debug) failed with exit code {code}"
                                );
                                return ExitCode::from(1);
                            }
                            times_d.push(ms);
                            out_d = out;
                        }
                        Err(e) => {
                            eprintln!("Error: {name} lykaon run (debug) failed: {}", e.message());
                            return ExitCode::from(1);
                        }
                    }
                }
                let _ = std::fs::remove_file(&lykaon_exe_d);
                times_d.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let median_d = times_d[times_d.len() / 2];

                // Lykaon fast (like-for-like): compile once (timed), then run 10x.
                let (lykaon_exe_f, compile_ms_f) = match lykaon::native_compile_to_exe(
                    &source,
                    lykaon_path.to_str().unwrap(),
                    "fast",
                    &bench_exe_dir,
                ) {
                    Ok(r) => r,
                    Err(e) => {
                        eprintln!(
                            "Error: {name} lykaon compile (fast) failed: {}",
                            e.message()
                        );
                        return ExitCode::from(1);
                    }
                };
                let _ = lykaon::run_exe(&lykaon_exe_f); // warm up
                let mut times_f: Vec<f64> = Vec::new();
                let mut out_f = String::new();
                for _ in 0..10 {
                    match lykaon::run_exe(&lykaon_exe_f) {
                        Ok((code, out, ms)) => {
                            if code != 0 {
                                eprintln!(
                                    "Error: {name} lykaon run (fast) failed with exit code {code}"
                                );
                                return ExitCode::from(1);
                            }
                            times_f.push(ms);
                            out_f = out;
                        }
                        Err(e) => {
                            eprintln!("Error: {name} lykaon run (fast) failed: {}", e.message());
                            return ExitCode::from(1);
                        }
                    }
                }
                let _ = std::fs::remove_file(&lykaon_exe_f);
                times_f.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let median_f = times_f[times_f.len() / 2];

                // Rust: run 10x (timed) and capture output checksum.
                let _ = lykaon::run_exe(&rust_exe); // warm up
                let mut rust_times_vec: Vec<f64> = Vec::new();
                let mut rust_out = String::new();
                for _ in 0..10 {
                    match lykaon::run_exe(&rust_exe) {
                        Ok((code, out, ms)) => {
                            if code != 0 {
                                eprintln!("Error: {name} rust run failed with exit code {code}");
                                return ExitCode::from(1);
                            }
                            rust_times_vec.push(ms);
                            rust_out = out.trim().to_string();
                        }
                        Err(e) => {
                            eprintln!("Error: {name} rust run failed: {}", e.message());
                            return ExitCode::from(1);
                        }
                    }
                }
                rust_times_vec.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let rust_median = rust_times_vec[rust_times_vec.len() / 2];

                // Verify Lykaon and Rust outputs match (checksum comparison).
                if out_f.trim() != rust_out {
                    eprintln!(
                        "Error: {name} checksum mismatch: Lykaon={out_f:?} Rust={rust_out:?}"
                    );
                    return ExitCode::from(1);
                }

                // The honest ratio divides by the Rust median measured in
                // THIS run (same exe-vs-exe method, same machine state),
                // not by the stored reference time. The stored reference is
                // only a cross-check: if the stored and measured Rust times
                // disagree by more than 2x, the stored file is stale.
                let ratio_d = median_d / rust_median;
                let ratio_f = median_f / rust_median;
                rat_d.push(ratio_d);
                rat_f.push(ratio_f);
                if rust_median < *rust_ms * 0.5 || rust_median > *rust_ms * 2.0 {
                    eprintln!(
                        "warning: {name} measured Rust time {rust_median:.1}ms differs from stored {} ms; update {name}.json entry",
                        rust_ms
                    );
                }

                println!(
                    "{}: lykaon_debug={:.1}ms (ratio {:.3}x) lykaon_fast={:.1}ms (ratio {:.3}x) rust={:.1}ms compile_d={:.1}ms compile_f={:.1}ms runs=10 checksum={} checks_removed={}",
                    name,
                    median_d,
                    ratio_d,
                    median_f,
                    ratio_f,
                    rust_median,
                    compile_ms_d,
                    compile_ms_f,
                    out_f.trim(),
                    checks,
                );
            }
            let gm_d: f64 = rat_d.iter().product::<f64>().powf(1.0 / rat_d.len() as f64);
            let gm_f: f64 = rat_f.iter().product::<f64>().powf(1.0 / rat_f.len() as f64);
            println!("contract prover checks removed across benchmarks: {checks_total}");
            println!("geometric mean ratio (default/debug): {gm_d:.3}x");
            println!("geometric mean ratio (like-for-like/fast): {gm_f:.3}x");
            ExitCode::from(0)
        }
        other => {
            eprintln!("unknown command: {other}");
            ExitCode::from(2)
        }
    }
}
