//! M4-8 (Appendix K 7.11): the tool's command-line arguments.
//!
//! `Takes NAME as T.` (M4-G25) and `Option NAME is T [defaulting to V].`
//! (M4-G26) declare what the program takes on its command line. The
//! parsing is shared by every runner (`lykaon run`, the built executable) so
//! both behave the same (M4-S82..S84):
//!
//! - positional arguments land in Takes order;
//! - flags are matched by option name with the words joined by `-`, the
//!   value after the name (`--log-level debug`) or after `=`
//!   (`--log-level=debug`); a flag with no value reads as 1 for the number
//!   kinds and the text "on" for text (the spec's --verbose, logged);
//! - `help` or `--help` as the first argument prints the usage text and
//!   exits 0 (M4-S84);
//! - a missing argument, an unknown option or a value of the wrong kind
//!   prints the usage text and exits 2 (M4-S83).

use crate::sem::{Program, ToolOpt, Value};

/// The usage-text error: the caller prints the text and exits 2.
pub struct UsageError {
    pub text: String,
}

/// The usage text (M4-S83): `usage: NAME` and then one line per Takes and
/// Option with its name, its kind, and required, optional or its default.
pub fn usage_text(prog: &Program, name: &str) -> String {
    let mut out = format!("usage: {name}\n");
    for t in &prog.takes {
        let kind = if t.maybe {
            format!("maybe {}", t.kind.word())
        } else {
            t.kind.word().to_string()
        };
        let req = if t.maybe { "optional" } else { "required" };
        out.push_str(&format!("  {} as {}, {}\n", t.name, kind, req));
    }
    for o in &prog.options {
        let kind = if o.maybe {
            format!("maybe {}", o.kind.word())
        } else {
            o.kind.word().to_string()
        };
        let tail = match (&o.default, o.maybe) {
            (Some(d), _) => format!("defaulting to {}", display_value(d)),
            (None, true) => "optional".to_string(),
            (None, false) => "required".to_string(),
        };
        out.push_str(&format!("  --{} as {}, {}\n", o.flag(), kind, tail));
    }
    out
}

/// A default value as the words it came from (the usage text's default).
fn display_value(v: &Value) -> String {
    match v {
        Value::Whole(n) => n.to_string(),
        Value::Dec(d) => {
            // the decimal's own printing, without a trailing .0 noise
            let s = d.to_string();
            s
        }
        Value::Text(t) => t.clone(),
        _ => String::new(),
    }
}

/// Parse the program's own arguments against its Takes/Option spec
/// (M4-S82). On success the bindings (name, value) in program order;
/// `help`/`--help` first is reported as the usage text with exit 0.
pub enum ToolArgs {
    Bindings(Vec<(String, Value)>),
    /// help or --help was asked: print the usage text, exit 0 (M4-S84).
    Help(String),
    /// Something is wrong with the usage: print the text, exit 2 (M4-S83).
    Bad(UsageError),
}

pub fn parse_tool_args(prog: &Program, name: &str, argv: &[String]) -> ToolArgs {
    // A program with no Takes and no Option declaration takes no command
    // line: its arguments are ignored (M4-S82 speaks of tools that
    // declare a spec; the differential runs pass none either way).
    if prog.takes.is_empty() && prog.options.is_empty() {
        return ToolArgs::Bindings(Vec::new());
    }
    if let Some(first) = argv.first() {
        if first == "help" || first == "--help" {
            return ToolArgs::Help(usage_text(prog, name));
        }
    }
    let mut binds: Vec<(String, Value)> = Vec::new();
    let mut pos = 0usize; // the next Takes slot
    let mut i = 0usize;
    while i < argv.len() {
        let a = &argv[i];
        if let Some(flag) = a.strip_prefix("--") {
            // --name[=value]
            let (word, inline) = match flag.split_once('=') {
                Some((w, v)) => (w.to_string(), Some(v.to_string())),
                None => (flag.to_string(), None),
            };
            let Some(opt) = prog.options.iter().find(|o| o.flag() == word) else {
                return ToolArgs::Bad(UsageError {
                    text: usage_text(prog, name),
                });
            };
            let value = match inline {
                Some(v) => match opt.kind.parse_word(&v) {
                    Some(val) => val,
                    None => {
                        return ToolArgs::Bad(UsageError {
                            text: usage_text(prog, name),
                        });
                    }
                },
                None => {
                    // the value after the name, when one follows and is not
                    // itself a flag (S82); with nothing after the name the
                    // flag stands bare (1 for the number kinds, "on" for
                    // text - the spec's --verbose, logged)
                    let next = argv.get(i + 1);
                    match next {
                        Some(n) if !n.starts_with("--") => {
                            // a value was given: the wrong kind is bad
                            // usage (M4-S83)
                            match opt.kind.parse_word(n) {
                                Some(val) => {
                                    i += 1;
                                    val
                                }
                                None => {
                                    return ToolArgs::Bad(UsageError {
                                        text: usage_text(prog, name),
                                    });
                                }
                            }
                        }
                        _ => opt.kind.bare_flag(),
                    }
                }
            };
            binds.push((opt.name.clone(), maybe_wrap(opt, value)));
            i += 1;
            continue;
        }
        // positional: the next Takes slot
        let Some(t) = prog.takes.get(pos) else {
            // more positionals than Takes: bad usage (M4-S83)
            return ToolArgs::Bad(UsageError {
                text: usage_text(prog, name),
            });
        };
        match t.kind.parse_word(a) {
            Some(val) => {
                binds.push((t.name.clone(), maybe_wrap_t(t.maybe, val)));
                pos += 1;
            }
            None => {
                return ToolArgs::Bad(UsageError {
                    text: usage_text(prog, name),
                });
            }
        }
        i += 1;
    }
    // required Takes left over: bad usage (M4-S83)
    if pos < prog.takes.len() && prog.takes[pos..].iter().any(|t| !t.maybe) {
        return ToolArgs::Bad(UsageError {
            text: usage_text(prog, name),
        });
    }
    // absent optional Takes and untouched Options: defaults and missing
    for t in &prog.takes {
        if !binds.iter().any(|(n, _)| n == &t.name) {
            binds.push((t.name.clone(), Value::Maybe(None)));
        }
    }
    for o in &prog.options {
        if !binds.iter().any(|(n, _)| n == &o.name) {
            let v = match &o.default {
                Some(d) => maybe_wrap(o, d.clone()),
                None => Value::Maybe(None),
            };
            binds.push((o.name.clone(), v));
        }
    }
    ToolArgs::Bindings(binds)
}

/// An option seeded value: a maybe option reads missing when its value is
/// the bare flag's "nothing"; the plain kinds read the value as-is.
fn maybe_wrap(o: &ToolOpt, v: Value) -> Value {
    maybe_wrap_t(o.maybe, v)
}

fn maybe_wrap_t(maybe: bool, v: Value) -> Value {
    if maybe {
        Value::Maybe(Some(Box::new(v)))
    } else {
        v
    }
}

/// Is `word` a usable tool name (T0171's path rule for Run): letters,
/// digits, . - _ and no path separators.
pub fn valid_prog_name(word: &str) -> bool {
    !word.is_empty()
        && !word.contains(['/', '\\', ':'])
        && word
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_'))
}
