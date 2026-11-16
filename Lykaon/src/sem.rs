//! Semantic layer (M1b): the typed tree (Ch.67: "a typed tree, then a
//! mid-level graph"). Builds a Program from the sentence tree, resolves names
//! and kinds (Ch.4, 6, 15, 17, 66), and reports the M1b semantic diagnostics:
//! T0205, T0301, T0302, T0303, T0406, T0509. The result feeds the mid-level
//! graph (mir.rs) and the interpreter (interp.rs).
//!
//! Check order (Ch.66, p.168): ambiguity (the syntax layer), names, types.
//! One main error per mistake: a sentence that already has an error gets no
//! follow-up errors.

use crate::diagnostics::Diagnostic;
use crate::lexer::{Lexer, Token};

use crate::pre_scan::NameTable;
use crate::splitter::Sentence;
use std::collections::HashMap;

pub use lykaon_core::sem::*;

// ---------------------------------------------------------------- scopes

#[derive(Clone, Debug)]
struct Def {
    kind: Kind,
    mutable: bool,
    shared: bool, // visible to other modules (ch.36)
}

#[derive(Clone, Debug, Default)]
struct Scope {
    defs: Vec<(String, Def)>,
    /// Task names defined in this block scope and its enclosing blocks
    /// (M4-G1/M4-D2): visible to Wait for NAME. and Stop task NAME.
    /// A block that is transparent for task names (M4-D2) passes its own
    /// task names back out (Do these together).
    tasks: Vec<String>,
}

impl Scope {
    fn child(&self) -> Scope {
        Scope {
            defs: self.defs.clone(),
            tasks: self.tasks.clone(),
        }
    }
    fn find(&self, name: &str) -> Option<Def> {
        self.defs
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, d)| d.clone())
    }
    fn define(&mut self, name: &str, d: Def) {
        self.defs.push((name.to_string(), d));
    }
    fn define_task(&mut self, name: &str) {
        self.tasks.push(name.to_string());
    }
    fn find_task(&self, name: &str) -> bool {
        self.tasks.iter().any(|t| t == name)
    }
    /// Tasks flow back OUT of a transparent-with-tasks block (M4-D2).
    fn take_tasks_back(&mut self, inner: Vec<String>) {
        for t in inner {
            if !self.tasks.contains(&t) {
                self.tasks.push(t);
            }
        }
    }
}

// ---------------------------------------------------------------- builder

pub fn build(
    all: &[Sentence],
    roots: &[usize],
    names: &NameTable,
    file: &str,
) -> (Program, Vec<Diagnostic>) {
    if std::env::var("Lykaon_DEBUG").is_ok() {
        eprintln!("DBG names={:?}", names.spellings());
    }
    let mut b = Builder {
        all,
        file: file.to_string(),
        source_dir: std::path::Path::new(file)
            .parent()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_default(),
        diags: Vec::new(),
        names: sorted_names(names),
        funcs: Vec::new(),
        func_names: Vec::new(),
        func_arity: Vec::new(),
        top_defs: Vec::new(), // filled right after, together with top_kinds
        top_kinds: HashMap::new(),
        err_reported: false,
        text_depth: 0,
        record_types: HashMap::new(),
        enum_types: HashMap::new(),
        shape_names: HashMap::new(),
        defining: None,
        in_can_fail_fn: false,
        fn_outer_changeables: Vec::new(),
        lent_live: Vec::new(),
        in_try: 0,
        in_task: 0,
        task_transfer: false,
        shared_names: Vec::new(),
        tests: Vec::new(),
        in_test: 0,
        in_fail_check: 0,
        interfaces: Vec::new(),
        impls: Vec::new(),
        always: Vec::new(),
        pending_tags: Vec::new(),
        give_as: None,
        package: None,
        package_file: std::path::Path::new(file)
            .file_name()
            .map(|s| s.eq_ignore_ascii_case("Lykaon.toml"))
            .unwrap_or(false),
        roots: roots.to_vec(),
        temp_names: Vec::new(),
        tool_sentence_idx: Vec::new(),
        in_serve: 0,
        in_handler: 0,
        in_live: 0,
        prev_one_line_fn: false,
        in_careful: 0,
        page_table: Vec::new(),
        fresh_kind: Kind::Unknown,
    };
    let (td, tk) = collect_top_defs(all, roots);
    b.top_defs = td;
    b.top_kinds = tk;
    for &idx in roots {
        b.hoist_types(idx);
    }
    // Interfaces are declared before their limits can be validated, so they
    // are hoisted like record and enum types (ch.23, M3-G7).
    for &idx in roots {
        b.hoist_interfaces(idx);
    }
    // Share <name>. names are collected before functions are parsed, so that
    // a shared function's input kinds are checked (T0330) regardless of
    // whether Share appears before or after its To in the file (ch.36).
    for &idx in roots {
        b.hoist_share(idx);
    }
    for &idx in roots {
        b.hoist_rec(idx, false);
    }
    // M4-8 (Appendix K 7.11): the Takes and Option sentences (M4-G25/G26)
    // are collected before the body builds: they stand before every other
    // sentence of the program except Note and About (T0174, M4-S81), and
    // they are removed from the body (their values are seeded at run
    // time, not sentences).
    let (takes, options) = b.parse_tool_decls(roots);
    let tool_idx = b.tool_sentence_idx.clone();
    // M4-10 (M4-G78/S59): the Page sentences are collected before the
    // body builds, so a Fetch address and a When someone sentence can
    // name a page written later in the file (S59 looks pages up in the
    // Page table).
    b.prescan_pages(roots);
    // the tool names join the multi-word name table, so a Say can read
    // them by spelling (the single-word ones resolve through the scope)
    for t in &takes {
        if t.name.contains(' ') {
            b.names.push(t.name.clone());
        }
    }
    for o in &options {
        if o.name.contains(' ') {
            b.names.push(o.name.clone());
        }
    }
    b.names.sort_by(|a, b| {
        b.split_whitespace()
            .count()
            .cmp(&a.split_whitespace().count())
            .then(b.len().cmp(&a.len()))
            .then(a.cmp(b))
    });
    b.names.dedup();
    let body_roots: Vec<usize> = roots
        .iter()
        .copied()
        .filter(|i| !tool_idx.contains(i))
        .collect();
    let mut sc = Scope::default();
    let mut env = OwnEnv::new();
    // the tool's names are defined before the body reads them
    for t in &takes {
        sc.define(
            &t.name,
            Def {
                kind: tool_kind_sc(t.kind),
                mutable: true,
                shared: false,
            },
        );
    }
    for o in &options {
        sc.define(
            &o.name,
            Def {
                kind: tool_kind_sc(o.kind),
                mutable: true,
                shared: false,
            },
        );
    }
    let body = b.build_block(&body_roots, &mut sc, false, &mut env);
    (
        Program {
            body,
            funcs: b.funcs,
            tests: b.tests,
            interfaces: b.interfaces,
            impls: b.impls,
            always: b.always,
            package: b.package,
            source_dir: b.source_dir.clone(),
            takes,
            options,
        },
        b.diags,
    )
}

/// M4-8: the scope kind of a tool kind (`number` holds the decimal kind;
/// a whole-looking value still seeds a whole value - logged).
fn tool_kind_sc(k: ToolKind) -> Kind {
    match k {
        ToolKind::Whole => Kind::Whole,
        ToolKind::Number | ToolKind::Decimal => Kind::Decimal,
        ToolKind::Text => Kind::Text,
    }
}

/// M4-6 (M4-G53): the five format words; `Some(word)` when the given
/// token word is one of them. The words are reserved here only where a
/// format sentence can start (after Read / Save ... as).
pub(crate) fn FORMAT_WORD(w: Option<&str>) -> Option<&'static str> {
    match w {
        Some("json") => Some("json"),
        Some("toml") => Some("toml"),
        Some("yaml") => Some("yaml"),
        Some("xml") => Some("xml"),
        Some("csv") => Some("csv"),
        _ => None,
    }
}

/// Multi-word names first, then by length, so the longest name wins (Ch.65).
fn sorted_names(nt: &NameTable) -> Vec<String> {
    let mut v: Vec<String> = nt.spellings();
    v.sort_by(|a, b| {
        b.split_whitespace()
            .count()
            .cmp(&a.split_whitespace().count())
            .then(b.len().cmp(&a.len()))
            .then(a.cmp(b))
    });
    v.dedup();
    v
}

/// Every top-level name and its Changeable flag, in file order. A top-level
/// function sees constants and fixed top-level names, not Changeable names
/// (Ch.15, p.52).
/// Every top-level name and its Changeable flag, in file order, plus a
/// rough kind for each fixed name (M4: guarded/atomic/counter/channel
/// names are read from the definition words, so the task-body scope can
/// seed the DECLARED kind - M4-D3 capture rules; everything else stays
/// Kind::Unknown exactly as before). A top-level function sees constants
/// and fixed top-level names, not Changeable names (Ch.15, p.52).
fn collect_top_defs(
    all: &[Sentence],
    roots: &[usize],
) -> (Vec<(String, bool)>, HashMap<String, Kind>) {
    let mut v = Vec::new();
    let mut kinds: HashMap<String, Kind> = HashMap::new();
    for &idx in roots {
        let s = &all[idx];
        let f = first_word_lower(&s.text);
        if f == "changeable" || f == "constant" {
            if let Some(n) = s.text.split_whitespace().nth(1) {
                v.push((
                    n.trim_end_matches('.').to_ascii_lowercase(),
                    f == "changeable",
                ));
            }
        } else if f != "to"
            && f != "if"
            && f != "say"
            && f != "ask"
            && f != "set"
            && f != "repeat"
            && f != "for"
            && f != "stop"
            && f != "skip"
            && f != "give"
            && f != "otherwise"
            && f != "note"
            && f != "about"
        {
            let words: Vec<&str> = s.text.split_whitespace().collect();
            if words.len() >= 2 {
                if let Some(pos) = words.iter().position(|w| w.eq_ignore_ascii_case("is")) {
                    let name = words[..pos].join(" ");
                    if !name.is_empty() {
                        // the first word of the value decides the shared
                        // kinds a task may capture (M4-S2, M4-D3); the
                        // real parse gives the exact kind later
                        let after: Vec<String> = words[pos + 1..]
                            .iter()
                            .map(|w| w.trim_end_matches('.').to_ascii_lowercase())
                            .collect();
                        let k = match after.first().map(|x| x.as_str()) {
                            Some("guarded") => Kind::Guarded(Box::new(Kind::Unknown)),
                            Some("atomic")
                                if after.get(1).map(|x| x.as_str()) == Some("number") =>
                            {
                                Kind::Atomic
                            }
                            Some("counter") => Kind::Counter,
                            Some("channel") if after.get(1).map(|x| x.as_str()) == Some("of") => {
                                Kind::Channel(Box::new(Kind::Unknown))
                            }
                            Some("share") if after.get(1).map(|x| x.as_str()) == Some("of") => {
                                Kind::Share
                            }
                            _ => Kind::Unknown,
                        };
                        let low = name.to_ascii_lowercase();
                        if !matches!(k, Kind::Unknown) {
                            kinds.insert(low.clone(), k);
                        }
                        v.push((low, false));
                    }
                }
            }
        }
    }
    (v, kinds)
}

struct Builder<'a> {
    all: &'a [Sentence],
    file: String,
    /// M4-S29: the folder relative file paths resolve against.
    source_dir: String,
    diags: Vec<Diagnostic>,
    names: Vec<String>,
    funcs: Vec<FuncDef>,
    func_names: Vec<String>,
    /// (name, input count, has defaulting-to) for compile-time input checks.
    func_arity: Vec<(String, usize, bool, Vec<Option<ParamType>>)>,
    top_defs: Vec<(String, bool)>,
    /// M4 (Appendix K): the rough declared kind of each fixed top-level
    /// name computed by collect_top_defs, so a task body's seeded scope
    /// carries the DECLARED kind for the M4-D3 shared kinds.
    top_kinds: HashMap<String, Kind>,
    err_reported: bool,
    /// 1 while parsing a value position (a definition value, a comparison
    /// value, the value after how many in / lower of): an unknown word there
    /// is text (Ch.4, rule 2). 0 in every other place: an unknown word is an
    /// operand of a math word and is an error (Ch.4, rule 3).
    text_depth: usize,
    /// Declared record types: person -> [(name, text), (age, number)] (ch.20).
    record_types: HashMap<String, Vec<(String, Kind)>>,
    /// Declared enums: payment -> [(cash, []), (card, [(owner, text)])] (ch.21).
    enum_types: HashMap<String, Vec<(String, Vec<(String, Kind)>)>>,
    /// A shape name -> its enum type and parts (ch.21).
    shape_names: HashMap<String, (String, Vec<(String, Kind)>)>,
    /// The name being defined right now: not in scope until its sentence ends
    /// (ch.20), so the name table must not match it in the definition value.
    defining: Option<String>,
    /// Failure-context flags for can-fail checking (ch.19):
    in_can_fail_fn: bool, // inside the body of a function declared can fail
    fn_outer_changeables: Vec<String>, // Changeable names the function may not see (T0204)
    lent_live: Vec<String>, // lend to change borrows live in the current sentence (T0404)
    in_try: usize,          // inside a Try block (can-fail sentences are handled)
    // ---- M4 (Appendix K) ----
    in_task: usize, // inside a Start task body (captures are T0451, M4-S2)
    /// A value position that hands the value over (Give back, Send): a
    /// move-kind capture is allowed there (T0450's "given").
    task_transfer: bool,
    shared_names: Vec<String>, // names marked Share (ch.36)
    tests: Vec<TestDef>,       // Test blocks collected at top level (ch.38)
    in_test: usize,            // inside a Test block (ch.38)
    in_fail_check: usize,      // inside a "Check that this fails." block
    // ---- M3 ----
    interfaces: Vec<Interface>, // Anything that can VERB must have FN. (ch.23)
    impls: Vec<ImplBlock>,      // A dog can speak. / A point can add. (ch.23, 26)
    always: Vec<(String, Contract)>, // Always ... under a record (ch.64)
    pending_tags: Vec<String>,  // Tagged NAME. before a definition (M3-S39)
    give_as: Option<ParamType>, // Give back ... as <type>. (M3-G19)
    package: Option<PackageDecl>, // Lykaon.toml facts (ch.37)
    package_file: bool,         // the file being built is an Lykaon.toml
    roots: Vec<usize>,          // the top-level sentences (ch.36)
    /// M4-G46: the names bound by Make temporary file, so a later `file
    /// <name>` resolves to the bound path (the temp binding wins).
    temp_names: Vec<String>,
    /// M4-8 (Appendix K 7.11): the top-level indices of the Takes and
    /// Option sentences, so the body build can skip them (their values
    /// are seeded at run time, not sentences).
    tool_sentence_idx: Vec<usize>,
    // ---- M4-10 (Appendix K 7.8 network) ----
    in_serve: usize,   // inside a Serve block (When someone/Respond live here)
    in_handler: usize, // inside a When someone body (Respond + request reads)
    in_live: usize,    // inside a When someone opens live body (connection)
    /// the sentence before the one being built is a one-line To function
    /// (T0161's "one-line To followed by Requires")
    prev_one_line_fn: bool,
    in_careful: usize, // inside a Be careful block (the TLS skip is legal)
    /// The Page table (M4-G78): page NAME -> the path pattern, scanned
    /// from the top-level Page sentences before the body builds.
    page_table: Vec<(String, Vec<PageSeg>)>,
    /// The compile kind of a fresh `it` (the response record after a
    /// Fetch or a Post, maybe text after a Receive from connection),
    /// so `status of it.` reads as a part read (S60).
    fresh_kind: Kind,
}

impl<'a> Builder<'a> {
    fn err(
        &mut self,
        code: &'static str,
        what: String,
        s: &Sentence,
        lo: usize,
        hi: usize,
        why: String,
        fix: String,
    ) {
        if self.err_reported {
            return;
        }
        self.err_reported = true;
        self.diags.push(Diagnostic::error(
            code,
            what,
            self.file.clone(),
            s.line,
            s.text.clone(),
            lo,
            hi,
            why,
            fix,
        ));
    }

    /// Like `err`, but tolerates a `None` sentence (used by the ownership
    /// checker, which checks expressions that may not carry a sentence span).
    fn err_opt(
        &mut self,
        code: &'static str,
        what: String,
        s: Option<&'a Sentence>,
        lo: usize,
        hi: usize,
        why: String,
        fix: String,
    ) {
        if let Some(ss) = s {
            self.err(code, what, ss, lo, hi, why, fix);
        }
    }

    // ------------------------------------------------------------ hoisting

    /// Register record and enum declarations before functions are parsed, so
    /// a function body can construct records (ch.20-21).
    fn hoist_types(&mut self, idx: usize) {
        let low = self.all[idx].text.to_ascii_lowercase();
        let words: Vec<&str> = low.split_whitespace().collect();
        let is_decl = words.len() >= 4
            && matches!(words[0], "a" | "an")
            && (words[2] == "has" || (words[2] == "is" && words.iter().any(|w| *w == "or")));
        if is_decl {
            let s = &self.all[idx];
            let (toks, _) = Lexer::new(&s.text).tokenize();
            let mut sc = Scope::default();
            let _ = self.parse_type_decl(s, &toks, &mut sc);
        }
        let children = self.all[idx].children.clone();
        for c in children {
            self.hoist_types(c);
        }
    }

    /// Register interface declarations ("Anything that can VERB must have FN.")
    /// before functions are parsed, so limits can name them (ch.23, M3-G7).
    fn hoist_interfaces(&mut self, idx: usize) {
        let low = self.all[idx].text.to_ascii_lowercase();
        let words: Vec<&str> = low.split_whitespace().collect();
        let is_interface = words.len() >= 6
            && words[0] == "anything"
            && words[1] == "that"
            && words[2] == "can"
            && words.iter().any(|w| *w == "must")
            && words.iter().any(|w| *w == "have");
        if is_interface {
            let s = &self.all[idx];
            let (toks, _) = Lexer::new(&s.text).tokenize();
            let _ = self.parse_interface_def(s, &toks);
        }
        let children = self.all[idx].children.clone();
        for c in children {
            self.hoist_interfaces(c);
        }
    }

    /// Collect `Share <name>.` names before functions are parsed, so a shared
    /// function's input kinds are checked (T0330) no matter the file order in
    /// which Share and its To appear (ch.36).
    fn hoist_share(&mut self, idx: usize) {
        let low = self.all[idx].text.to_ascii_lowercase();
        let words: Vec<&str> = low.split_whitespace().collect();
        if words.first() == Some(&"share") && words.len() >= 2 {
            let name = words[1..].join(" ").trim_end_matches('.').to_string();
            if !self.shared_names.iter().any(|n| n == &name) {
                self.shared_names.push(name);
            }
        }
        let children = self.all[idx].children.clone();
        for c in children {
            self.hoist_share(c);
        }
    }

    fn hoist_rec(&mut self, idx: usize, in_impl: bool) {
        let first = first_word_lower(&self.all[idx].text);
        if first == "to" {
            let s = &self.all[idx];
            // The hoist is a dry run: it registers the name, and the real
            // build parses the function again. parse_function consumes the
            // pending result kind (`give_as`), so the dry run must not take
            // it away from the real parse - otherwise no function ever has
            // its stated result kind (T0331, M3-S9).
            let saved_kind = self.give_as.take();
            let parsed = self.parse_function(s, in_impl);
            self.give_as = saved_kind;
            if let Some(f) = parsed {
                let name = f.name.clone();
                if !in_impl {
                    self.funcs.push(f);
                }
                // Impl methods are callable by interface dispatch (ch.23): the
                // name must still be recognized as a function so a call inside
                // another body compiles and then routes to eval_interface_call.
                self.func_names.push(name);
            }
        }
        // A dog can speak. (an impl block): its To children belong to the
        // impl, not to the program's function list (ch.23).
        let lower_text = self.all[idx].text.to_ascii_lowercase();
        let words: Vec<&str> = lower_text.split_whitespace().collect();
        let this_is_impl = words.len() >= 4 && matches!(words[0], "a" | "an") && words[2] == "can";
        let children = self.all[idx].children.clone();
        for c in children {
            self.hoist_rec(c, this_is_impl);
        }
    }

    fn top_seed_scope(&self) -> Scope {
        let mut sc = Scope::default();
        for (n, mutable) in self.top_defs.clone() {
            if mutable {
                continue; // a top-level function does not see a Changeable name
            }
            // M4 (Appendix K): seed the DECLARED kind where the pre-pass
            // could read it, so the M4-D3 shared kinds (guarded, atomic,
            // counter, channel, share) carry their kind into a task body.
            let k = self.top_kinds.get(&n).cloned().unwrap_or(Kind::Unknown);
            sc.define(
                &n,
                Def {
                    kind: k,
                    mutable: false,
                    shared: false,
                },
            );
        }
        sc
    }

    /// Parse `To <name> <input> [with <input>]... [defaulting to <v>]
    /// [can fail] [give <expr>.]` or the block form.
    fn parse_function(&mut self, s: &'a Sentence, in_impl: bool) -> Option<FuncDef> {
        let (toks, _) = Lexer::new(&s.text).tokenize();
        let mut ts = TS::new(&toks);
        ts.pos += 1; // To
        let name = ts.peek_word()?.to_ascii_lowercase();
        ts.pos += 1;
        let mut inputs: Vec<(String, ParamMode)> = Vec::new();
        let mut input_types: Vec<Option<ParamType>> = Vec::new();
        // first input: the word straight after the name
        if ts.peek_word() == Some("lend") {
            // To pad lend to change items. (Ch.28): lend to change is a unique
            // borrow, the input is the word after change.
            ts.pos += 1;
            if ts.consume_word("to") && ts.consume_word("change") {
                if let Some(w) = ts.peek_word() {
                    inputs.push((w.to_ascii_lowercase(), ParamMode::LentToChange));
                    ts.pos += 1;
                }
            }
        } else if ts.peek_word() == Some("give") && ts.peek_next() != Some("back") {
            // To f give items. (Ch.28): the input is moved in.
            ts.pos += 1;
            if let Some(w) = ts.peek_word() {
                inputs.push((w.to_ascii_lowercase(), ParamMode::MoveIn));
                ts.pos += 1;
            }
        } else if let Some(w) = ts.peek_word() {
            if !matches!(w, "with" | "can" | "defaulting" | "as") {
                inputs.push((w.to_ascii_lowercase(), ParamMode::Lent));
                ts.pos += 1;
            }
        }
        loop {
            match ts.peek_word() {
                Some("as") => {
                    ts.pos += 1;
                    // stated input kind (M3-G2/G3): whole number, number,
                    // decimal, text, or a limit (M3-G4)
                    let pt = self.parse_param_type(&mut ts);
                    if let Some(i) = inputs.len().checked_sub(1) {
                        if input_types.len() <= i {
                            input_types.resize(inputs.len(), None);
                        }
                        input_types[i] = pt;
                    }
                    // an "as" with no preceding input word is malformed; the
                    // kind is simply not bound here and later checks decide
                }
                Some("with") => {
                    ts.pos += 1;
                    match ts.peek_word() {
                        Some("give") => {
                            ts.pos += 1;
                            if let Some(w) = ts.peek_word() {
                                inputs.push((w.to_ascii_lowercase(), ParamMode::MoveIn));
                                ts.pos += 1;
                            }
                        }
                        Some("lend") => {
                            ts.pos += 1;
                            if ts.consume_word("to") && ts.consume_word("change") {
                                if let Some(w) = ts.peek_word() {
                                    inputs.push((w.to_ascii_lowercase(), ParamMode::LentToChange));
                                    ts.pos += 1;
                                }
                            }
                        }
                        Some(w) if !matches!(w, "give" | "can" | "defaulting" | "as") => {
                            inputs.push((w.to_ascii_lowercase(), ParamMode::Lent));
                            ts.pos += 1;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        // input_types parallels inputs: every input starts untyped (None);
        // an `as <kind>` phrase fills its slot (M3-G2).
        input_types.resize(inputs.len(), None);
        let mut default_last = None;
        if ts.peek_word() == Some("defaulting") {
            ts.pos += 1;
            ts.consume_word("to");
            if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
                // the default value for the LAST input (Ch.15)
                self.text_depth += 1;
                default_last =
                    Some(self.parse_expr(ts.rest_without_period(), None, &Scope::default(), false));
                self.text_depth -= 1;
            }
        }
        let can_fail = if ts.peek_word() == Some("can") {
            ts.pos += 1;
            ts.consume_word("fail");
            true
        } else {
            false
        };
        // the function's own name is visible in its body (recursion, Ch.15);
        // its input count is recorded for the compile-time call check (Ch.66)
        self.func_names.push(name.clone());
        self.func_arity.push((
            name.clone(),
            inputs.len(),
            default_last.is_some(),
            input_types.clone(),
        ));
        let mut requires: Vec<Contract> = Vec::new();
        let mut ensures: Vec<Contract> = Vec::new();
        let body: FnBody = if ts.peek_word() == Some("give") {
            ts.pos += 1;
            if ts.peek_word() == Some("back") {
                ts.pos += 1;
            }
            let rest = ts.rest_without_period();
            // `give back <value> as <kind>.` states the result kind on the
            // one-line form too (M3-G19); the value keeps the phrase, which
            // is also the run-time conversion.
            let mut typed = rest.clone();
            if let Some(pt) = self.take_trailing_as(&mut typed) {
                self.give_as = Some(pt);
            }
            let mut fsc = self.top_seed_scope();
            for i in &inputs {
                fsc.define(
                    &i.0,
                    Def {
                        kind: Kind::Unknown,
                        mutable: false,
                        shared: false,
                    },
                );
            }
            FnBody::Expr({
                // the given value is a value position (Ch.4, rule 2)
                self.text_depth += 1;
                let e = self.parse_expr(rest, Some(s), &fsc, false);
                self.text_depth -= 1;
                e
            })
        } else {
            let mut fsc = self.top_seed_scope();
            let mut env = OwnEnv::new();
            for (n, mode) in &inputs {
                fsc.define(
                    n,
                    Def {
                        kind: Kind::Unknown,
                        mutable: true,
                        shared: false,
                    },
                );
                env.vars.insert(
                    n.clone(),
                    VarState {
                        kind: Kind::Unknown,
                        mutable: true,
                        alive: true,
                        mode: *mode,
                    },
                );
                env.params.push(n.clone());
            }
            // a function does not see outer Changeable names (T0204, ch.66)
            let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
            self.fn_outer_changeables = self
                .top_defs
                .iter()
                .filter(|(_, m)| *m)
                .map(|(n, _)| n.clone())
                .collect();
            let saved_cf = self.in_can_fail_fn;
            self.in_can_fail_fn = can_fail;
            // Contracts stand first in a block function (M3-G24): leading
            // Requires/Ensures sentences are pulled out of the body.
            let mut contract_children: Vec<usize> = Vec::new();
            let mut rest_children: Vec<usize> = Vec::new();
            let mut in_contracts = true;
            for &c in &s.children {
                let fw = first_word_lower(&self.all[c].text);
                if in_contracts && (fw == "requires" || fw == "ensures") {
                    contract_children.push(c);
                } else {
                    in_contracts = false;
                    rest_children.push(c);
                }
            }
            for &c in &contract_children {
                let cs = &self.all[c];
                let (ctoks, _) = Lexer::new(&cs.text).tokenize();
                let mut cts = TS::new(&ctoks);
                let is_ensures = first_word_lower(&cs.text) == "ensures";
                cts.pos += 1; // Requires / Ensures
                let checked = cts.consume_word("checked");
                let mut cond_sc = fsc.clone();
                if is_ensures {
                    cond_sc.define(
                        "result",
                        Def {
                            kind: Kind::Unknown,
                            mutable: false,
                            shared: false,
                        },
                    );
                }
                let cond = self.parse_condition(cts.rest_without_period(), Some(cs), &cond_sc);
                let ct = Contract {
                    cond,
                    checked,
                    is_ensures,
                    line: cs.line,
                    text: cs.text.trim().trim_end_matches('.').to_string(),
                };
                if is_ensures {
                    ensures.push(ct);
                } else {
                    requires.push(ct);
                }
            }
            let body = self.build_block(&rest_children, &mut fsc, false, &mut env);
            self.in_can_fail_fn = saved_cf;
            self.fn_outer_changeables = saved_oc;
            FnBody::Block(body)
        };
        let shared = self.shared_names.contains(&name);
        let tags = std::mem::take(&mut self.pending_tags);
        for t in &tags {
            if !matches!(t.as_str(), "test" | "deprecated" | "slow") {
                self.err(
                    "T0162",
                    "Unknown tag.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A tag other than test, deprecated or slow is not defined.".to_string(),
                    "Use a listed tag.".to_string(),
                );
                break;
            }
        }
        let is_generator = body_has_hand_back(&body);
        // T0317 (M3-G26): branches of a function give different kinds
        if let FnBody::Block(stmts) = &body {
            let give_kind = |st: &Stmt| -> Option<Kind> {
                match st {
                    Stmt::GiveBack(Some(v)) => Some(v.kind.clone()),
                    _ => None,
                }
            };
            for st in stmts {
                if let Stmt::If { branches, other } = st {
                    let then_kinds: Vec<Kind> = branches
                        .iter()
                        .filter_map(|(_, b)| b.iter().find_map(give_kind))
                        .collect();
                    let else_kinds: Vec<Kind> = other
                        .iter()
                        .flat_map(|b| b.iter())
                        .filter_map(give_kind)
                        .collect();
                    let comparable = |k: &Kind| !matches!(k, Kind::Unknown | Kind::Missing);
                    let mut all: Vec<Kind> = then_kinds
                        .iter()
                        .chain(else_kinds.iter())
                        .cloned()
                        .collect();
                    all.retain(|k| comparable(k));
                    let differs = all.windows(2).any(|w| w[0] != w[1]);
                    if differs {
                        let (lo, hi) = span_of(&s.text, &name);
                        self.err(
                            "T0317",
                            "Result kind differs.".to_string(),
                            s,
                            lo,
                            hi,
                            "Branches of a function give different kinds.".to_string(),
                            "Give one kind.".to_string(),
                        );
                        break;
                    }
                }
            }
        }
        // T0157 (ch.15/M3): a function has no input. A generator is the
        // exception (the classic infinite source `To naturals. ... Hand
        // back` has no input by design; M3's conformance uses it).
        if inputs.is_empty() && !is_generator {
            let (lo, hi) = span_of(&s.text, &name);
            self.err(
                "T0157",
                "Function with no input.".to_string(),
                s,
                lo,
                hi,
                "A function has no input.".to_string(),
                "Give it an input.".to_string(),
            );
        }
        // T0163 (ch.25/M3): a generator mixed with Give back
        let has_give_back = match &body {
            FnBody::Block(stmts) => stmts.iter().any(|st| matches!(st, Stmt::GiveBack(_))),
            FnBody::Expr(_) => false,
        };
        if is_generator && has_give_back {
            let (lo, hi) = span_of(&s.text, &name);
            self.err(
                "T0163",
                "Generator mixed with Give back.".to_string(),
                s,
                lo,
                hi,
                "A function has both Hand back and Give back.".to_string(),
                "Use one.".to_string(),
            );
        }
        let result_type = self.give_as.take();
        // M3-S9: a shared function or a recursive function must state the
        // kinds of its inputs (T0330); a recursive function must state its
        // result kind (T0331, deferred - see LYKAON_DEVIATIONS.md).
        let recursive = Self::fn_body_mentions_call_to(&body, &name);
        let must_state_kinds = shared || recursive;
        if must_state_kinds && input_types.iter().any(Option::is_none) {
            let (lo, hi) = span_of(&s.text, &name);
            self.err("T0330", format!("{name} must state the kinds of its inputs."), s, lo, hi,
                "A shared function, an interface function, or a recursive function must state the kind of each input.".to_string(),
                "Write as <kind> after each input.".to_string());
        }
        // M3-S9 / T0331: a recursive function states its result kind (the
        // ch.15 sumto example ends each Give back with `as whole number`).
        // The stated kind is what the recursion is checked against, so an
        // unstated one is refused rather than inferred.
        if recursive && result_type.is_none() {
            let (lo, hi) = span_of(&s.text, &name);
            self.err(
                "T0331",
                "Result kind missing.".to_string(),
                s,
                lo,
                hi,
                "A recursive function does not state its result kind.".to_string(),
                "End it with as whole number.".to_string(),
            );
        }
        // M3-S11 / T0324: the verb of a limit must name a declared interface
        // (Anything that can VERB must have FN.).
        for pt in &input_types {
            if let Some(ParamType::Limited(verbs)) = pt.as_ref() {
                for v in verbs {
                    if !self.interfaces.iter().any(|i| i.verb == *v) {
                        // T0164 (M3): the limit names no interface. The book
                        // keeps T0324 for "Limit not met" (a kind that cannot
                        // satisfy a declared limit), so this is its own code.
                        let (lo, hi) = {
                            let (a, b) = name_span(&s.text, v);
                            if a == b { (0, s.text.len()) } else { (a, b) }
                        };
                        self.err(
                            "T0164",
                            "Limit names no interface.".to_string(),
                            s,
                            lo,
                            hi,
                            format!("anything that can {v} where no interface {v} exists"),
                            "Declare it.".to_string(),
                        );
                    }
                }
            }
        }
        // Captures: fixed top-level names visible where this function is
        // written, minus its own inputs (the closure's shared borrow, ch.24).
        let captures: Vec<String> = self
            .top_defs
            .iter()
            .filter(|(n, _)| *n != name && !inputs.iter().any(|(i, _)| i == n))
            .map(|(n, _)| n.clone())
            .collect();
        Some(FuncDef {
            name,
            inputs,
            can_fail,
            default_last,
            body,
            shared,
            input_types,
            result_type,
            requires,
            ensures,
            tags,
            is_generator,
            is_local: false,
            captures,
        })
    }

    /// Does the expression tree contain a call to the function named `name`?
    /// Used to detect recursion (T0330/T0331).
    fn expr_mentions_call_to(e: &Expr, name: &str) -> bool {
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(cur) = stack.pop() {
            if let E::Call { name: called, .. } = &cur.e {
                if called == name {
                    return true;
                }
            }
            stack.extend(Self::expr_children(cur));
        }
        false
    }

    /// The immediate child expressions of an expression (for tree walking).
    fn expr_children(e: &Expr) -> Vec<&Expr> {
        match &e.e {
            E::Call { args, .. } => args.iter().collect(),
            E::Neg(x)
            | E::Round(x, _)
            | E::Factorial(x)
            | E::Reverse(x)
            | E::Unique(x)
            | E::AsWhole(x)
            | E::AsDecimal(x)
            | E::AsBig(x)
            | E::AsText(x)
            | E::AsNumber(x)
            | E::AsMaybe(x)
            | E::CopyOf(x)
            | E::Move(x)
            | E::Share(x)
            | E::WeakShare(x)
            | E::Trimmed(x)
            | E::Normalized(x)
            | E::Upper(x)
            | E::Lower(x)
            | E::CountIn(x)
            | E::LastOf(x)
            | E::IsEmpty(x) => vec![x],
            E::Binary { l, r, .. } => vec![l, r],
            E::DivWhole(l, r) => vec![l, r],
            E::Rem(l, r) => vec![l, r],
            E::Pow(l, r) => vec![l, r],
            E::AndOr(l, r, ..) => vec![l, r],
            E::Fallback { value, default, .. } => vec![value, default],
            E::JoinedWith(value, ..) => vec![value],
            E::PartOf { base, .. } => vec![base],
            E::ItemN { list, n, .. } => vec![list, n],
            E::SafeItemN { list, n, .. } => vec![list, n],
            E::ItemsRange { list, from, to, .. } => vec![list, from, to],
            E::FirstN { list, n, .. } => vec![list, n],
            E::FirstFib(n) | E::PrimesTo(n) => vec![n],
            E::AsDyn { value, .. } => vec![value],
            E::PositionOf {
                haystack, needle, ..
            } => vec![haystack, needle],
            E::ValueOf { map, key, .. } => vec![map, key],
            E::Has { coll, item, .. } => vec![coll, item],
            E::Union { a, b, .. } | E::Overlap { a, b, .. } | E::Difference { a, b, .. } => {
                vec![a, b]
            }
            E::Split { text, sep, .. } => vec![text, sep],
            E::Replace {
                pat, repl, text, ..
            } => vec![pat, repl, text],
            E::ListOf(items) | E::MinMax { items, .. } | E::Flat(items) => items.iter().collect(),
            E::PairOf(a, b) => vec![a, b],
            E::RecordOf { parts, .. } | E::EnumOf { parts, .. } => {
                parts.iter().map(|(_, e)| e).collect()
            }
            E::ApplyEach { list, .. } | E::Combine { list, .. } => vec![list],
            E::FirstOf(x) | E::SecondOf(x) => vec![x],
            E::Sorted(x, _) => vec![x],
            E::Where { list, cond, .. } => vec![list, cond],
            E::Whole(_)
            | E::Dec(_)
            | E::Boolean(_)
            | E::Missing
            | E::Word(_)
            | E::Name(_)
            | E::It
            | E::Them
            | E::FnRef(_)
            | E::PatWords { .. }
            | E::CollEmpty { .. }
            | E::Compare(_)
            | E::AtomicNum
            | E::CounterZero
            | E::ChannelOf { .. } => Vec::new(),
            // M4 (Appendix K): guarded V walks into V
            E::GuardedOf(x) => vec![x],
            // M4-5 (Appendix K 7.5): a file question reads the disk; it
            // holds no expression (the words of the path)
            // M4-6 (7.6): json of x's one child belongs to the walk too.
            E::JsonOf(x) => vec![x],
            // M4-10 (7.8): a request read carries only a name; no child.
            E::RequestRead { .. } => Vec::new(),
            E::FileExists(_) => Vec::new(),
            // M4-7 (7.7): the time and secret reads walk their one
            // child; the literal date, today, now, the duration value
            // and random decimal hold none.
            E::MomentAt { date, .. }
            | E::InZone { base: date, .. }
            | E::TimeShift { base: date, .. }
            | E::RandomItem { list: date }
            | E::Shuffled { list: date }
            | E::HashOf(date)
            | E::SecretOf(date)
            | E::Reveal(date) => vec![date],
            E::DaysBetween { a, b } | E::SecondsBetween { a, b } | E::RandomRange { a, b } => {
                vec![a, b]
            }
            E::DateCtor { .. } | E::Today | E::Now | E::DurationOf { .. } | E::RandomDec => {
                Vec::new()
            }
            // M4-8 (7.10/7.11): the environment read and the input read
            // carry no expression children
            E::Environment { .. } | E::ReadInput => Vec::new(),
        }
    }

    /// Does a statement subtree call the function `name`? Recurses into
    /// nested statements (loops, ifs, try blocks, checks, tests).
    fn stmt_mentions_call_to(s: &Stmt, name: &str) -> bool {
        match s {
            Stmt::Say { expr, .. } => Self::expr_mentions_call_to(expr, name),
            Stmt::Define(d) => Self::expr_mentions_call_to(&d.expr, name),
            Stmt::Set { expr, .. } => Self::expr_mentions_call_to(expr, name),
            Stmt::Ask {
                fallback: Some(e), ..
            }
            | Stmt::Fail { message: e, .. } => Self::expr_mentions_call_to(e, name),
            Stmt::Ask { .. } => false,
            Stmt::If { branches, other } => {
                branches.iter().any(|(e, ss)| {
                    Self::expr_mentions_call_to(e, name)
                        || ss.iter().any(|s| Self::stmt_mentions_call_to(s, name))
                }) || other
                    .iter()
                    .any(|ss| ss.iter().any(|s| Self::stmt_mentions_call_to(s, name)))
            }
            Stmt::RepeatTimes { count: e, body } | Stmt::RepeatWhile { cond: e, body } => {
                Self::expr_mentions_call_to(e, name)
                    || body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::RepeatForever { body } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::ForRange { from, to, body, .. } => {
                Self::expr_mentions_call_to(from, name)
                    || Self::expr_mentions_call_to(to, name)
                    || body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::ForIn { list, body, .. } => {
                Self::expr_mentions_call_to(list, name)
                    || body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                Self::stmt_mentions_call_to(sentence, name)
                    || success.iter().any(|s| Self::stmt_mentions_call_to(s, name))
                    || failure
                        .iter()
                        .any(|(_, ss)| ss.iter().any(|s| Self::stmt_mentions_call_to(s, name)))
            }
            Stmt::Check { cond, body, .. } => {
                cond.iter().any(|e| Self::expr_mentions_call_to(e, name))
                    || body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::Test { body, .. } => body.iter().any(|s| Self::stmt_mentions_call_to(s, name)),
            Stmt::Evaluate { expr, .. } => Self::expr_mentions_call_to(expr, name),
            Stmt::Append { value: e, .. }
            | Stmt::Put {
                value: e,
                key: None,
                ..
            }
            | Stmt::Remove { value: e, .. }
            | Stmt::SetPart { expr: e, .. } => Self::expr_mentions_call_to(e, name),
            Stmt::Put {
                key: Some(k),
                value: e,
                ..
            } => Self::expr_mentions_call_to(k, name) || Self::expr_mentions_call_to(e, name),
            Stmt::LookAt { value, whens, .. } => {
                Self::expr_mentions_call_to(value, name)
                    || whens
                        .iter()
                        .any(|w| w.body.iter().any(|s| Self::stmt_mentions_call_to(s, name)))
            }
            Stmt::HandBack(e) => Self::expr_mentions_call_to(e, name),
            Stmt::GiveBack(e) => e.iter().any(|e| Self::expr_mentions_call_to(e, name)),
            Stmt::Close { .. }
            | Stmt::Share { .. }
            | Stmt::Use { .. }
            | Stmt::Stop
            | Stmt::Skip
            | Stmt::PassFailureUp
            | Stmt::DefineEnum { .. }
            | Stmt::Note
            | Stmt::RemoveFirst { .. }
            | Stmt::Pretend { .. } => false,
            Stmt::DefineLocalFn(f) => Self::fn_body_mentions_call_to(&f.body, name),
            // M4 (Appendix K): a task block mentioning the callee counts as
            // calling it (the body is a call edge for reachability).
            Stmt::StartTask { body, .. } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::DoTogether { body } => body.iter().any(|s| Self::stmt_mentions_call_to(s, name)),
            Stmt::WaitFor { .. } | Stmt::StopTask { .. } | Stmt::SleepFor { .. } => false,
            // M4 (Appendix K): Send/AtomicAdd carry expressions; Receive
            // carries only the channel name
            Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => {
                Self::expr_mentions_call_to(value, name)
            }
            Stmt::Receive { .. } => false,
            // M4-4 (Appendix K 7.3/7.4): timer, stream and spread sentences
            // walk into their bodies (the body runs later or inline, but
            // its calls are still calls of the enclosing reachability);
            // Use N workers. carries no expression.
            Stmt::AfterTimer { body, .. }
            | Stmt::EveryTimer { body, .. }
            | Stmt::StreamLoop { body, .. }
            | Stmt::Spread { body, .. } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::UseWorkers { .. } => false,
            // M4-7 (7.7): Use seed carries no expression.
            Stmt::UseSeed { .. } => false,
            // M4-8 (7.10/7.11): the Run arguments are calls of the
            // enclosing reachability; the signal and input loop bodies
            // walk; Exit carries only a literal code.
            Stmt::RunProc { args, .. } => args.iter().any(|e| Self::expr_mentions_call_to(e, name)),
            Stmt::Log { expr, .. } => Self::expr_mentions_call_to(expr, name),
            // M4-9 (7.12): Use log level touches no value and calls
            // nothing.
            Stmt::LogLevel { .. } => false,
            // M4-10 (7.8): the fetch/post/send values are calls of the
            // enclosing reachability; the server bodies walk.
            Stmt::Fetch {
                data,
                headers,
                query,
                ..
            } => {
                data.as_ref()
                    .map(|d| Self::expr_mentions_call_to(d, name))
                    .unwrap_or(false)
                    || headers
                        .iter()
                        .any(|(_, e)| Self::expr_mentions_call_to(e, name))
                    || query
                        .iter()
                        .any(|(_, e)| Self::expr_mentions_call_to(e, name))
            }
            Stmt::PostTo { data, .. } => Self::expr_mentions_call_to(data, name),
            Stmt::WsSend { value } => Self::expr_mentions_call_to(value, name),
            Stmt::Respond { kind, .. } => match kind {
                RespondKind::Text(e) | RespondKind::Json(e) | RespondKind::Literally(e) => {
                    Self::expr_mentions_call_to(e, name)
                }
                RespondKind::Status(_, Some(e)) => Self::expr_mentions_call_to(e, name),
                RespondKind::Status(_, None) | RespondKind::Template(_) => false,
            },
            Stmt::Serve { body, .. }
            | Stmt::WhenSomeone { body, .. }
            | Stmt::WhenLive { body, .. } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => false,
            Stmt::Careful { body } => body.iter().any(|s| Self::stmt_mentions_call_to(s, name)),
            Stmt::Exit { .. } => false,
            Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            // M4-5 (Appendix K 7.5): the write/append/replace value is an
            // expression of the enclosing reachability; the loop/watch
            // bodies walk; the other file sentences hold only literal
            // path words.
            Stmt::WriteFile { value, .. }
            | Stmt::AppendFile { value, .. }
            | Stmt::ReplaceFile { value, .. } => Self::expr_mentions_call_to(value, name),
            Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => {
                body.iter().any(|s| Self::stmt_mentions_call_to(s, name))
            }
            // M4-6: the save value and the from-text decode source read
            // like the write value; the file reads hold only path words
            Stmt::SaveFormat { value, .. } | Stmt::ReadFormatText { value, .. } => {
                Self::expr_mentions_call_to(value, name)
            }
            Stmt::ReadFile { .. }
            | Stmt::ReadBytes { .. }
            | Stmt::ListFolder { .. }
            | Stmt::MakeFolder { .. }
            | Stmt::RemovePath { .. }
            | Stmt::MovePath { .. }
            | Stmt::DuplicatePath { .. }
            | Stmt::MakeTempFile { .. }
            | Stmt::ZipOp { .. }
            | Stmt::ReadFormat { .. } => false,
        }
    }

    /// Does a function body contain a call to `name` (recursion)?
    fn fn_body_mentions_call_to(body: &FnBody, name: &str) -> bool {
        match body {
            FnBody::Block(stmts) => stmts.iter().any(|s| Self::stmt_mentions_call_to(s, name)),
            FnBody::Expr(e) => Self::expr_mentions_call_to(e, name),
        }
    }

    /// A stated parameter type (M3-G3): a kind, or a limit

    /// A stated parameter type (M3-G3): a kind, or a limit
    /// `anything that can VERB [and VERB]` (M3-G4). The limit ends at the
    /// verb, which is one word; a with after it starts the next input (M3-D3).
    fn parse_param_type(&mut self, ts: &mut TS) -> Option<ParamType> {
        // optional leading "whole" as in `as whole number`
        if ts.peek_word() == Some("whole") {
            ts.pos += 1;
            if ts.peek_word() == Some("number") {
                ts.pos += 1;
                return Some(ParamType::K(Kind::Whole));
            }
            ts.pos -= 1;
            return Some(ParamType::K(Kind::Whole));
        }
        match ts.peek_word() {
            Some("number") => {
                ts.pos += 1;
                Some(ParamType::Number)
            }
            Some("decimal") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Decimal))
            }
            Some("text") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Text))
            }
            Some("truth") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Boolean))
            }
            Some("letter") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Letter))
            }
            // ---- M4-7 (Appendix K 7.7): the time and secret kinds ----
            Some("date") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Date))
            }
            Some("moment") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Moment))
            }
            Some("duration") => {
                ts.pos += 1;
                Some(ParamType::K(Kind::Duration))
            }
            Some("secret") => {
                ts.pos += 1;
                // the secret of text (bytes are not values yet - logged)
                if ts.peek_word() == Some("text") {
                    ts.pos += 1;
                }
                Some(ParamType::K(Kind::Secret(Box::new(Kind::Text))))
            }
            Some("anything") => {
                ts.pos += 1;
                if ts.peek_word() != Some("that") {
                    return Some(ParamType::Any);
                }
                ts.pos += 1;
                if !ts.consume_word("can") {
                    return Some(ParamType::Any);
                }
                let mut verbs = Vec::new();
                // the limit ends at the verb: one word (M3-D3)
                if let Some(v) = ts.peek_word() {
                    if !matches!(v, "with" | "can" | "defaulting" | "as" | "give" | "and") {
                        verbs.push(v.to_string());
                        ts.pos += 1;
                    }
                }
                if ts.peek_word() == Some("and") {
                    ts.pos += 1;
                    if ts.peek_word() == Some("can") {
                        ts.pos += 1;
                    }
                    if let Some(v) = ts.peek_word() {
                        if !matches!(v, "with" | "can" | "defaulting" | "as" | "give") {
                            verbs.push(v.to_string());
                            ts.pos += 1;
                        }
                    }
                }
                if verbs.is_empty() {
                    Some(ParamType::Any)
                } else {
                    Some(ParamType::Limited(verbs))
                }
            }
            _ => None,
        }
    }

    /// Compile-time call check (Ch.66): a call gives exactly as many inputs
    /// as the function has, unless the missing one is last with defaulting to.
    /// T0316 (M3-G26): an input of a kind the function does not accept.
    fn check_arity(&mut self, name: &str, got: usize, arg_kinds: &[Kind], s: Option<&'a Sentence>) {
        let Some(ss) = s else { return };
        let Some((want, has_def, input_kinds)) = self
            .func_arity
            .iter()
            .rev()
            .find(|(n, _, _, _)| n == name)
            .map(|(_, w, d, ks)| (*w, *d, ks.clone()))
        else {
            return;
        };
        let ok = got == want || (has_def && got + 1 == want);
        if !ok {
            self.err(
                "T0126",
                "A call gives more or fewer inputs than the function has.".to_string(),
                ss,
                0,
                ss.text.len(),
                "A call gives more or fewer inputs than the function has.".to_string(),
                "Match the inputs of the function.".to_string(),
            );
            return;
        }
        // T0316: an input of a kind the function does not accept (the
        // stated kinds only; an unstated input accepts anything)
        for (i, k) in input_kinds.iter().enumerate() {
            let Some(want) = k else { continue };
            let Some(got_kind) = arg_kinds.get(i) else {
                continue;
            };
            let comparable = |x: &Kind| !matches!(x, Kind::Unknown | Kind::Missing);
            // Number accepts any number kind; Any/Limited accept anything
            let kind_ok = match want {
                // an unknown argument kind is not checked (the call's
                // result kind is not tracked in the registry)
                ParamType::K(kind) => {
                    !comparable(got_kind) || (comparable(kind) && kind == got_kind)
                }
                ParamType::Number => matches!(got_kind, Kind::Whole | Kind::Decimal | Kind::Big),
                ParamType::Any | ParamType::Limited(_) => true,
            };
            if !kind_ok {
                self.err(
                    "T0316",
                    "Input kind differs.".to_string(),
                    ss,
                    0,
                    ss.text.len(),
                    "An input is of a kind the function does not accept.".to_string(),
                    "Give the right kind.".to_string(),
                );
                return;
            }
        }
    }

    // ------------------------------------------------------------ blocks

    /// Build a block of statements into Stmt values. `fresh_result` seeds the
    /// Ch.16 pronoun state: inside a Try success block, `it` refers to the
    /// try sentence's result (ch.19).
    fn build_block(
        &mut self,
        indices: &[usize],
        sc: &mut Scope,
        fresh_result_seed: bool,
        env: &mut OwnEnv,
    ) -> Vec<Stmt> {
        let mut out: Vec<Stmt> = Vec::new();
        let mut i = 0;
        // Ch.16 pronoun state: it/them refer to the sentence just before.
        let mut fresh_result = fresh_result_seed;
        let mut fresh_is_list = false;
        let mut prev_shown = String::new();
        // M4-10 (S60): a fresh it starts kindless in every block; the
        // sentence builders read it (the response record after a Fetch).
        self.fresh_kind = Kind::Unknown;
        while i < indices.len() {
            let idx = indices[i];
            let s = &self.all[idx];
            let first = first_word_lower(&s.text);
            self.err_reported = false; // one main error per sentence

            // The lexer refuses a line with a quote, a comma, an invalid
            // character or a name that begins with a digit; its diagnostic
            // surfaces here (raw-text sentences and the text-taking words
            // Note/About keep their punctuation, ch.3, and are not lexed
            // strictly).
            let fw = s
                .text
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_ascii_lowercase();
            let text_taking = matches!(fw.as_str(), "note" | "about");
            // the Run sentence's own name rules live in this layer's Run
            // arm (its lexer-error handling is the designed T0113)
            let sem_owns = fw == "run";
            // a tab is the splitter's own T0001 (one error per mistake)
            if !s.is_raw_text && !text_taking && !sem_owns && !s.text.contains('\t') {
                if let Some(d) = Lexer::new(&s.text).tokenize().1 {
                    let code = d.code;
                    let what = d.what.clone();
                    let why = d.why.clone();
                    let fix = d.fix.clone();
                    let (lo, hi) = (d.mark_lo, d.mark_hi);
                    self.err(code, what, s, lo, hi, why, fix);
                    i += 1;
                    continue;
                }
            }

            // Later-milestone sentences fail with T0509 and never crash.
            if let Some(msg) = later_milestone_shape(&s.text) {
                self.err(
                    "T0509",
                    "A sentence belongs to a later milestone.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    msg,
                    "Wait until its milestone.".to_string(),
                );
                i += 1;
                continue;
            }
            match first.as_str() {
                "if" => {
                    let stmts = self.build_if(indices, &mut i, sc, env);
                    out.extend(stmts);
                    continue;
                }
                "try" => {
                    // Try <sentence that can fail>. Then optional If that fails
                    // blocks follow as siblings (ch.19).
                    let all_toks = toks_of(&s.text);
                    let mut ts = TS::new(&all_toks);
                    ts.pos += 1; // try
                    let sentence_toks = ts.rest_without_period();
                    let sentence_empty = sentence_toks.is_empty();
                    // M2-S15 / T0151: Try wraps a sentence that can fail. A
                    // sentence can fail only if it calls a function declared
                    // can fail (or is an Ask/conversion). The block form
                    // (Try. with nothing after it) is exempt.
                    let sentence_can_fail = sentence_toks.iter().any(|t| match t {
                        Token::Word { lower, .. } => lower == "close" || self.func_can_fail(lower),
                        _ => false,
                    });
                    if !sentence_empty && !sentence_can_fail {
                        self.err(
                            "T0151",
                            "Try wraps a sentence that cannot fail.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Say, and most sentences, cannot fail.".to_string(),
                            "Remove Try, or wrap a sentence that can fail.".to_string(),
                        );
                    }
                    let sentence = if sentence_empty {
                        Stmt::Note
                    } else if matches!(sentence_toks.first(), Some(Token::Word { lower, .. }) if lower == "close")
                    {
                        // Try Close notes. keeps the Close statement (and its
                        // ownership effects), not a plain expression (ch.31)
                        self.parse_close(Some(s), &sentence_toks, sc)
                    } else {
                        Stmt::Evaluate {
                            expr: self.parse_expr(sentence_toks, Some(s), sc, false),
                            list: false,
                        }
                    };
                    self.in_try += 1;
                    let success = self.build_block(&s.children, sc, true, env);
                    self.in_try -= 1;
                    // consume following "If that fails [with KIND]."
                    let mut failure: Vec<(Option<String>, Vec<Stmt>)> = Vec::new();
                    while i + 1 < indices.len() {
                        let os = &self.all[indices[i + 1]];
                        let ow = first_word_lower(&os.text);
                        if ow != "if" {
                            break;
                        }
                        let lw: Vec<&str> = os
                            .text
                            .split_whitespace()
                            .map(|w| w.trim_end_matches('.'))
                            .collect();
                        if lw.len() < 3 || lw[1] != "that" || lw[2] != "fails" {
                            break;
                        }
                        i += 1;
                        let mut kind: Option<String> = None;
                        if lw.len() >= 5 && lw[3] == "with" {
                            kind = Some(lw[4..].join(" "));
                        }
                        self.in_try += 1;
                        let body = self.build_block(&os.children, sc, false, env);
                        self.in_try -= 1;
                        failure.push((kind, body));
                    }
                    out.push(Stmt::Try {
                        sentence: Box::new(sentence),
                        success,
                        failure,
                    });
                    i += 1;
                    continue;
                }
                "otherwise" => {
                    i += 1; // the syntax layer already reported
                    continue;
                }
                "test" => {
                    // Test <name>. block (ch.38): everything after "test" is the
                    // name as raw text. Tests are collected for `lykaon test` and
                    // left in the body as no-ops for `lykaon run`.
                    self.in_test += 1;
                    let body = self.build_block(&s.children, sc, false, env);
                    self.in_test -= 1;
                    let test_name = text_after_first_word(&s.text);
                    self.tests.push(TestDef {
                        name: test_name.clone(),
                        body: body.clone(),
                    });
                    out.push(Stmt::Test {
                        name: test_name,
                        body,
                    });
                    i += 1;
                    continue;
                }
                "check" => {
                    // "Check that this fails." opens a block (ch.38); the check
                    // passes when a sentence inside the block fails.
                    let low = s.text.to_ascii_lowercase();
                    let is_fail_check = low.contains("this fails");
                    if is_fail_check {
                        self.in_test += 1;
                        self.in_fail_check += 1;
                        let body = self.build_block(&s.children, sc, false, env);
                        self.in_fail_check -= 1;
                        self.in_test -= 1;
                        out.push(Stmt::Check {
                            text: s.text.clone(),
                            cond: None,
                            must_fail: true,
                            prop: None,
                            body,
                        });
                        i += 1;
                        continue;
                    }
                    // a plain `Check ...` falls through to build_one; a property
                    // check keeps its body (ch.38)
                    if low.starts_with("check for any") {
                        // "check for any <kind words...> <name>" â€” define the
                        // generated name so the body can use it
                        let words: Vec<&str> = low.split_whitespace().collect();
                        let (kind_words, gen_name) = if words.len() >= 5 {
                            let name = words[words.len() - 1].trim_end_matches('.');
                            (words[3..words.len() - 1].join(" "), name.to_string())
                        } else {
                            (String::new(), String::new())
                        };
                        let k = prop_kind(&kind_words);
                        if !gen_name.is_empty() {
                            sc.define(
                                &gen_name,
                                Def {
                                    kind: k,
                                    mutable: false,
                                    shared: false,
                                },
                            );
                        }
                        self.in_test += 1;
                        let body = self.build_block(&s.children, sc, false, env);
                        self.in_test -= 1;
                        let mut stmt = self.build_one(s, sc, env);
                        if let Stmt::Check {
                            prop: Some(_),
                            body: ref mut b,
                            ..
                        } = stmt
                        {
                            *b = body;
                        }
                        out.push(stmt);
                        i += 1;
                        continue;
                    }
                    // a plain `Check ...` falls through to build_one
                }
                "to" => {
                    // A To inside a block is a local function and a closure
                    // (M3-D2). Top-level functions are hoisted before this
                    // pass, so any To here that is not a file root is local.
                    if !self.roots.contains(&idx) {
                        let s = &self.all[idx];
                        if let Some(mut f) = self.parse_function(s, true) {
                            f.is_local = true;
                            out.push(Stmt::DefineLocalFn(f));
                        }
                    }
                    i += 1; // hoisted or local
                    continue;
                }
                "give" => {
                    let stmt =
                        Stmt::GiveBack(self.parse_give_tokens(&toks_of(&s.text), &*sc, Some(s)));
                    // ch.28-31: a give back is checked too (T0409: no borrow
                    // leaves the function)
                    self.check_stmt(&stmt, env, Some(s));
                    out.push(stmt);
                    i += 1;
                    continue;
                }
                // ---- M4 (Appendix K) task sentences with blocks ----
                "start" => {
                    let low = s.text.to_ascii_lowercase();
                    let words: Vec<&str> = low.split_whitespace().collect();
                    let words: Vec<&str> = words.iter().map(|w| w.trim_end_matches('.')).collect();
                    if words.get(1) == Some(&"task") {
                        let name: String = words[2..].join(" ");
                        if name.is_empty() {
                            self.err(
                                "T0113",
                                "A task sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "Start task does not name a task.".to_string(),
                                "Write Start task <name>. with a name.".to_string(),
                            );
                            i += 1;
                            continue;
                        }
                        // The task body sees fixed names only (M4-S2): a
                        // fresh function-like scope; a Changeable capture is
                        // T0451 (checked at the read site below).
                        let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
                        self.fn_outer_changeables = self
                            .top_defs
                            .iter()
                            .filter(|(_, m)| *m)
                            .map(|(n, _)| n.clone())
                            .collect();
                        self.in_task += 1;
                        let mut tsc = self.top_seed_scope();
                        let body = self.build_block(&s.children, &mut tsc, false, env);
                        self.in_task -= 1;
                        self.fn_outer_changeables = saved_oc;
                        sc.define_task(&name);
                        // M4-S2 / T0450: a task body may not carry a plain
                        // move-kind value from outside into the task (the
                        // book's "a plain list used by two tasks"). A value
                        // handed over (Give back / Send) is given, and a
                        // Share, guarded, atomic, counter or channel name is
                        // shared, so those are allowed.
                        self.check_task_value_crossing(s);
                        // M4-S2 / T0462: the task's name (its handle) belongs
                        // to the block it was started in - it may not be kept
                        // by being returned or stored.
                        self.check_task_handle_escape(&name, s);
                        out.push(Stmt::StartTask { name, body });
                        i += 1;
                        continue;
                    }
                    // some other sentence starting with "do"-like "start":
                    // parsed by the regular path below
                }
                "do" => {
                    let low = s.text.to_ascii_lowercase();
                    let words: Vec<&str> = low.split_whitespace().collect();
                    let words: Vec<&str> = words.iter().map(|w| w.trim_end_matches('.')).collect();
                    if words.get(1) == Some(&"these") && words.get(2) == Some(&"together") {
                        // M4-D2: the block is transparent for task names -
                        // a task started inside is visible (and waitable)
                        // after the block; regular names are not
                        let mut inner = sc.child();
                        let body = self.build_block(&s.children, &mut inner, false, env);
                        sc.take_tasks_back(inner.tasks.clone());
                        out.push(Stmt::DoTogether { body });
                        i += 1;
                        continue;
                    }
                }
                // ---- M4-4 (Appendix K 7.3/7.4): the timer, stream and
                // spread sentences with blocks ----
                "after" | "every" => {
                    let toks = toks_of(&s.text);
                    let every = first == "every";
                    let mut ts = TS::new(&toks);
                    ts.pos += 1; // after / every
                    let Some((amount, unit)) = self.parse_duration(Some(s), &toks[1..]) else {
                        i += 1;
                        continue;
                    };
                    ts.pos += 1; // the number
                    ts.pos += 1; // the unit
                    // the sentence ends after the unit; the body is indented
                    if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
                        self.err("T0113", "A timer sentence cannot be read.".to_string(), s, 0, s.text.len(),
                            "Only the number and the unit belong on the timer line; the steps go on the lines under it.".to_string(),
                            "Write After 5 seconds. with its body indented under it.".to_string());
                        i += 1;
                        continue;
                    }
                    // The timer body uses the task capture rules (logged
                    // choice: the book does not spell them for timers).
                    let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
                    self.fn_outer_changeables = self
                        .top_defs
                        .iter()
                        .filter(|(_, m)| *m)
                        .map(|(n, _)| n.clone())
                        .collect();
                    self.in_task += 1;
                    let mut tsc = self.top_seed_scope();
                    let body = self.build_block(&s.children, &mut tsc, false, env);
                    self.in_task -= 1;
                    self.fn_outer_changeables = saved_oc;
                    if every {
                        out.push(Stmt::EveryTimer { amount, unit, body });
                    } else {
                        out.push(Stmt::AfterTimer { amount, unit, body });
                    }
                    i += 1;
                    continue;
                }
                "spread" => {
                    let words: Vec<&str> = s
                        .text
                        .split_whitespace()
                        .map(|w| w.trim_end_matches('.'))
                        .collect();
                    if words
                        .get(1)
                        .map(|w| !w.eq_ignore_ascii_case("each"))
                        .unwrap_or(true)
                        || words
                            .get(2)
                            .map(|w| !w.eq_ignore_ascii_case("of"))
                            .unwrap_or(true)
                    {
                        self.err(
                            "T0113",
                            "A spread sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The spread reads Spread each of <a list> over workers.".to_string(),
                            "Write Spread each of the numbers over workers.".to_string(),
                        );
                        i += 1;
                        continue;
                    }
                    let toks = toks_of(&s.text);
                    let mut ts = TS::new(&toks);
                    ts.pos += 3; // spread each of
                    let items_toks = ts.rest_until_word("over");
                    let items = self.parse_expr(items_toks, Some(s), sc, false);
                    if !ts.consume_word("over") {
                        self.err(
                            "T0113",
                            "A spread sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The spread needs over workers. after the list.".to_string(),
                            "Write Spread each of the numbers over workers.".to_string(),
                        );
                        i += 1;
                        continue;
                    }
                    let trailing = ts.rest_without_period();
                    let ok_workers = trailing.len() == 1
                        && matches!(&trailing[0], Token::Word { lower, .. } if lower == "workers");
                    if !ok_workers {
                        self.err(
                            "T0113",
                            "A spread sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The spread line ends with the word workers.".to_string(),
                            "Write Spread each of the numbers over workers.".to_string(),
                        );
                        i += 1;
                        continue;
                    }
                    // M4-S24: the capture rules are the task's.
                    let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
                    self.fn_outer_changeables = self
                        .top_defs
                        .iter()
                        .filter(|(_, m)| *m)
                        .map(|(n, _)| n.clone())
                        .collect();
                    self.in_task += 1;
                    let mut tsc = self.top_seed_scope();
                    // it is the item (M4-S23): the body seeds fresh it
                    let body = self.build_block(&s.children, &mut tsc, true, env);
                    self.in_task -= 1;
                    self.fn_outer_changeables = saved_oc;
                    out.push(Stmt::Spread { items, body });
                    i += 1;
                    continue;
                }
                _ => {}
            }
            // T0161: the sentence before this one is a one-line To function
            // (the dispatcher cannot see the index; the loop provides it)
            self.prev_one_line_fn = i > 0 && {
                let p = &self.all[indices[i - 1]];
                first_word_lower(&p.text) == "to"
                    && p.children.is_empty()
                    && p.text.contains(" give ")
            };
            let stmt = self.build_one(s, sc, env);
            // M4-10 (S60): the kind a fresh `it` carries one sentence
            // later (the response record after a Fetch or a Post).
            self.fresh_kind = match &stmt {
                Stmt::Fetch { .. } | Stmt::PostTo { .. } => response_kind(),
                Stmt::WsRecv { .. } => Kind::Maybe(Box::new(Kind::Text)),
                _ => Kind::Unknown,
            };
            // Ch.16: "Say it." / "Say them." reach one sentence back only.
            if let Some(pron) = pure_pronoun(&stmt) {
                if !fresh_result {
                    let msg = if prev_shown.is_empty() {
                        "it means the result of the sentence just before. Give the result a name."
                            .to_string()
                    } else {
                        format!(
                            "it means the result of the sentence just before, and the sentence before printed {prev_shown}. Give the result a name."
                        )
                    };
                    self.err(
                        "T0220",
                        msg,
                        s,
                        0,
                        s.text.len(),
                        "it is used when the sentence before did not give a result.".to_string(),
                        "Name the result.".to_string(),
                    );
                } else if pron == "it" && fresh_is_list {
                    self.err(
                        "T0221",
                        "it is used for a list. Use them.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "it is used for a list.".to_string(),
                        "Use them.".to_string(),
                    );
                }
            }
            match &stmt {
                Stmt::Evaluate { list, .. } => {
                    fresh_result = true;
                    fresh_is_list = *list;
                }
                // M4-S4 (Appendix K): the wait result is it.
                Stmt::WaitFor { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                // M4-S13 (Appendix K): the received value is it.
                Stmt::Receive { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                // M4-S23 (Appendix K): the spread results are them, in
                // item order.
                Stmt::Spread { .. } => {
                    fresh_result = true;
                    fresh_is_list = true;
                }
                // M4-5 (7.5): Read file. leaves the text in it; Read bytes
                // of file. and List files in folder. leave a list.
                Stmt::ReadFile { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                Stmt::ReadBytes { .. } | Stmt::ListFolder { .. } => {
                    fresh_result = true;
                    fresh_is_list = true;
                }
                // M4-6 (7.6): a format read leaves the decoded value in it
                Stmt::ReadFormat { .. } | Stmt::ReadFormatText { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                // M4-8 (7.10): the started program's standard output is it.
                // For each line in input. is a loop like For each line in
                // file: the line is the loop's own name, not it.
                Stmt::RunProc { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                // M4-10 (7.8): the response record is it (status, body,
                // headers); a post is one too; a received live frame is
                // it (maybe text).
                Stmt::Fetch { .. } | Stmt::PostTo { .. } | Stmt::WsRecv { .. } => {
                    fresh_result = true;
                    fresh_is_list = false;
                }
                _ => {
                    fresh_result = false;
                    fresh_is_list = false;
                }
            }
            if let Stmt::Say { expr, .. } = &stmt {
                prev_shown = static_say_text(expr);
            }
            // "If that fails use X." attaches to the previous can-fail sentence.
            if matches!(
                stmt,
                Stmt::Define(..) | Stmt::Ask { .. } | Stmt::Evaluate { .. } | Stmt::Try { .. }
            ) {
                if let Some(next) = indices.get(i + 1).copied() {
                    if let Some(fb) = self.parse_fallback(&self.all[next], sc) {
                        // T0152: a definition's fallback default must match the
                        // defined value's kind (ch.19).
                        if let Stmt::Define(ref d) = stmt {
                            if d.expr.kind != Kind::Unknown
                                && d.expr.kind != Kind::Missing
                                && fb.kind != Kind::Unknown
                                && fb.kind != Kind::Missing
                                && d.expr.kind != fb.kind
                            {
                                self.err(
                                    "T0152",
                                    "fallback gives a different kind from the value.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    format!(
                                        "The fallback default does not match the kind of {}.",
                                        d.name
                                    ),
                                    "Use a value of the same kind.".to_string(),
                                );
                            }
                        }
                        i += 1;
                        out.push(with_fallback(stmt, fb));
                        i += 1;
                        continue;
                    }
                }
            }
            // "If that fails use X." after a sentence that gives no value is
            // T0152: there is no result to recover (ch.19).
            if !matches!(stmt, Stmt::Note) {
                if let Some(next) = indices.get(i + 1).copied() {
                    if let Some(fb) = self.parse_fallback(&self.all[next], sc) {
                        self.err(
                            "T0152",
                            "Recovery with no value.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "If that fails use follows a sentence that gives no value.".to_string(),
                            "Use Try and an If that fails block instead.".to_string(),
                        );
                        i += 1;
                        continue;
                    }
                }
            }
            // ch.19: a can-fail sentence needs Try, an "If that fails use" fallback,
            // or to be inside a can fail function (M2-S15, T0311). Inside a
            // "Check that this fails." block the failure is the point (ch.38).
            if self.in_try == 0
                && self.in_fail_check == 0
                && !self.in_can_fail_fn
                && !matches!(stmt, Stmt::Note)
                && stmt_can_fail(&stmt)
            {
                self.err(
                    "T0311",
                    "A can fail operation is used without Try or a default.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A can fail operation is used where its failure is not handled.".to_string(),
                    "Wrap it in Try and add an If that fails block, or use If that fails use."
                        .to_string(),
                );
            }
            // ch.28-31: ownership and borrowing (checked per sentence).
            self.check_stmt(&stmt, env, Some(s));
            out.push(stmt);
            i += 1;
        }
        out
    }

    /// `If that fails use <value>.` after a can-fail sentence.
    fn parse_fallback(&mut self, s: &'a Sentence, sc: &Scope) -> Option<Expr> {
        let ws: Vec<&str> = s.text.split_whitespace().collect();
        if ws.len() < 4
            || !ws[0].eq_ignore_ascii_case("if")
            || !ws[1].eq_ignore_ascii_case("that")
            || !ws[2].eq_ignore_ascii_case("fails")
        {
            return None;
        }
        // allowed forms: If that fails use X. / give X. ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â "use" per Ch.17
        if !ws[3].eq_ignore_ascii_case("use") && !ws[3].eq_ignore_ascii_case("give") {
            return None;
        }
        let toks = toks_of(&s.text);
        let mut ts = TS::new(&toks);
        ts.pos += 4; // if that fails use
        // the fallback default is a value position (Ch.4, rule 2): an unknown
        // word there is text
        let rest = ts.rest_without_period();
        self.text_depth += 1;
        let fb = if rest.is_empty() {
            flat_empty()
        } else {
            self.parse_expr(rest, Some(s), sc, true)
        };
        self.text_depth -= 1;
        Some(fb)
    }

    fn build_if(
        &mut self,
        indices: &[usize],
        i: &mut usize,
        sc: &mut Scope,
        env: &mut OwnEnv,
    ) -> Vec<Stmt> {
        let idx = indices[*i];
        let s = &self.all[idx];
        // "If that fails use X." was consumed by the previous statement.
        let ws: Vec<&str> = s.text.split_whitespace().collect();
        if ws.len() >= 3
            && ws[1].eq_ignore_ascii_case("that")
            && ws[2].trim_end_matches('.').eq_ignore_ascii_case("fails")
        {
            *i += 1;
            return vec![];
        }
        let (toks, _) = Lexer::new(&s.text).tokenize();
        let mut ts = TS::new(&toks);
        ts.pos += 1; // if

        if !s.children.is_empty() {
            let cond = self.parse_condition(ts.rest_without_period(), Some(s), &*sc);
            let mut body_env = env.clone();
            let body = self.build_block(&s.children, &mut sc.child(), false, &mut body_env);
            let mut branches = vec![(cond, body, body_env)];
            let mut other = None;
            *i += 1;
            while *i < indices.len() {
                let os_idx = indices[*i];
                let os = &self.all[os_idx];
                if first_word_lower(&os.text) != "otherwise" {
                    break;
                }
                let (otoks, _) = Lexer::new(&os.text).tokenize();
                let mut ots = TS::new(&otoks);
                ots.pos += 1; // otherwise
                if ots.peek_word() == Some("if") {
                    ots.pos += 1;
                    let c = self.parse_condition(ots.rest_without_period(), Some(os), &*sc);
                    let mut be = env.clone();
                    let b = self.build_block(&os.children, &mut sc.child(), false, &mut be);
                    branches.push((c, b, be));
                } else {
                    let mut be = env.clone();
                    let b = self.build_block(&os.children, &mut sc.child(), false, &mut be);
                    other = Some((b, be));
                }
                *i += 1;
            }
            self.err_reported = false;
            // Join: a name survives only if alive in every branch (ch.28).
            let mut joined = env.clone();
            for (name, v) in &env.vars {
                let alive_all = branches
                    .iter()
                    .all(|(_, _, be)| be.vars.get(name).map_or(false, |v2| v2.alive))
                    && other.as_ref().map_or(true, |(_, be)| {
                        be.vars.get(name).map_or(false, |v2| v2.alive)
                    });
                if let Some(v) = joined.vars.get_mut(name) {
                    v.alive = alive_all;
                }
            }
            *env = joined;
            vec![Stmt::If {
                branches: branches.into_iter().map(|(c, b, _)| (c, b)).collect(),
                other: other.map(|(b, _)| b),
            }]
        } else {
            let cond_toks = ts.rest_until_one_line_action();
            let cond = self.parse_condition(cond_toks, Some(s), &*sc);
            let stmt = self.parse_inline_body(ts.rest_without_period(), Some(s), sc);
            let mut branches = vec![(cond, vec![stmt])];
            let mut other: Option<Vec<Stmt>> = None;
            *i += 1;
            // a one-line If still pairs with a following Otherwise (Ch.9)
            while *i < indices.len() {
                let os_idx = indices[*i];
                let os = &self.all[os_idx];
                if first_word_lower(&os.text) != "otherwise" {
                    break;
                }
                let (otoks, _) = Lexer::new(&os.text).tokenize();
                let mut ots = TS::new(&otoks);
                ots.pos += 1; // otherwise
                if ots.peek_word() == Some("if") {
                    ots.pos += 1;
                    let c = self.parse_condition(ots.rest_until_one_line_action(), Some(os), &*sc);
                    let st = self.parse_inline_body(ots.rest_without_period(), Some(os), sc);
                    branches.push((c, vec![st]));
                } else {
                    let st = self.parse_inline_body(ots.rest_without_period(), Some(os), sc);
                    other = Some(vec![st]);
                }
                *i += 1;
            }
            self.err_reported = false;
            vec![Stmt::If { branches, other }]
        }
    }

    /// One-line body statement after If/Repeat/For each on the same line.
    fn parse_inline_body(
        &mut self,
        toks: Vec<Token>,
        s: Option<&'a Sentence>,
        sc: &mut Scope,
    ) -> Stmt {
        if toks.is_empty() {
            return Stmt::Note;
        }
        let lower = match &toks[0] {
            Token::Word { lower, .. } => lower.clone(),
            _ => return Stmt::Note,
        };
        match lower.as_str() {
            "say" => self.parse_say(toks[1..].to_vec(), s, sc, true),
            "set" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1;
                let name = self.match_name(&mut ts).unwrap_or_default();
                if ts.peek_word() == Some("to") {
                    ts.pos += 1;
                }
                let expr = self.parse_expr(ts.rest_without_period(), s, sc, false);
                if let Some(d) = sc.find(&name) {
                    if !d.mutable {
                        // M4-D3 (Appendix K): a guarded name is fixed but
                        // changes through Set - an authorized change; an
                        // atomic or counter changes with Add only.
                        if !matches!(d.kind, Kind::Guarded(_)) {
                            if let Some(ss) = s {
                                let (lo, hi) = span_of(&ss.text, &name);
                                if matches!(d.kind, Kind::Atomic | Kind::Counter) {
                                    self.err("T0406", format!("{name} is fixed and cannot be changed."), ss, lo, hi,
                                        format!("{name} is an atomic number or counter; it changes with Add, not Set."),
                                        format!("Add <number> to {name}. or Add <number> to {name} atomically."));
                                } else {
                                    self.err(
                                        "T0406",
                                        format!("{name} is fixed and cannot be changed."),
                                        ss,
                                        lo,
                                        hi,
                                        format!("{name} was defined without Changeable."),
                                        format!("Define it as Changeable {name} is <first value>."),
                                    );
                                }
                            }
                        }
                    }
                }
                Stmt::Set { name, expr }
            }
            "give" => Stmt::GiveBack(self.parse_give_tokens(&toks, sc, s)),
            "stop" => {
                // M4-G19: Stop task NAME. is the cancel request (the inline
                // one-line-rest form has no task members to check, so it
                // passes the name through unchecked)
                let low = match s {
                    Some(ss) => ss.text.to_ascii_lowercase(),
                    None => String::new(),
                };
                let words: Vec<&str> = low.split_whitespace().collect();
                if words.get(1) == Some(&"task") {
                    match words[2..].join(" ") {
                        n if !n.is_empty() => return Stmt::StopTask { name: n },
                        _ => Stmt::Note,
                    }
                } else {
                    Stmt::Stop
                }
            }
            "skip" => Stmt::Skip,
            "fail" => self.parse_fail(s, &toks, sc),
            "pass" => self.parse_pass(s, &toks, sc),
            _ => Stmt::Note,
        }
    }

    /// Split a trailing `as <kind>` off a value token list (M3-G19). The
    /// kind phrase is at most three words (`as anything that can speak` is
    /// the limit form; the plain kinds are two). Returns the stated kind.
    fn take_trailing_as(&mut self, rest: &mut Vec<Token>) -> Option<ParamType> {
        for k in 1..=3.min(rest.len()) {
            let split = rest.len() - k;
            if split == 0 {
                continue;
            }
            let is_as =
                matches!(rest.get(split - 1), Some(Token::Word { lower, .. }) if lower == "as");
            if !is_as {
                continue;
            }
            let mut trial = TS::new(rest);
            trial.pos = split;
            if let Some(pt) = self.parse_param_type(&mut trial) {
                // the phrase stays in the value: `X as whole number` is also
                // a run-time conversion (M3-G19 records the kind as well)
                return Some(pt);
            }
        }
        None
    }

    fn parse_give_tokens(
        &mut self,
        toks: &[Token],
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Option<Expr> {
        let mut ts = TS::new(toks);
        ts.pos += 1;
        if ts.peek_word() == Some("back") {
            ts.pos += 1;
        }
        if matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            return None;
        }
        // Give back <value> as <type>. (M3-G19): a trailing `as <type>` is
        // the stated result kind, recorded for the function (M3-S9)
        // Give back <value> as <type>. (M3-G19): a trailing `as <type>` is
        // the stated result kind, recorded for the function (M3-S9)
        let rest = ts.rest_without_period();
        let mut typed = rest.clone();
        if let Some(pt) = self.take_trailing_as(&mut typed) {
            self.give_as = Some(pt);
        }
        // the given value is a value position (Ch.4, rule 2): give back
        // negative. gives the text negative
        let was_transfer = self.task_transfer;
        self.task_transfer = true;
        self.text_depth += 1;
        let e = self.parse_expr(rest, s, sc, false);
        self.text_depth -= 1;
        self.task_transfer = was_transfer;
        Some(e)
    }

    /// M4-S2 / T0450 (the book's "a plain list used by two tasks"): the
    /// body of a Start task may read copy-kind values, but a plain move-kind
    /// value (a list, map, set, record, queue) may cross only by being
    /// handed over (Give back / Send) or by being shared, guarded or atomic.
    /// The capture is decided from the body's words at the Start task
    /// sentence, which is where the task boundary is drawn.
    /// Is the top-level name defined with a move-kind value (a list, map,
    /// set, queue or a record made with is a <kind>)? The declared-kind map
    /// does not carry these literal definitions, so the definition sentence
    /// is read directly (the kind words are fixed).
    fn defined_as_move_kind(&self, name: &str) -> bool {
        let prefix = format!("{name} is ");
        for &idx in &self.roots {
            let text = self.all[idx].text.to_ascii_lowercase();
            let Some(rest) = text.strip_prefix(&prefix) else {
                continue;
            };
            let first = rest.split_whitespace().next().unwrap_or("");
            return match first {
                "list" | "map" | "set" | "queue" => true,
                // a record, enum variant or pair is a made value
                "a" | "an" => true,
                _ => false,
            };
        }
        false
    }

    fn check_task_value_crossing(&mut self, s: &'a Sentence) {
        // the body text, every indented line under the Start task
        let all = self.all;
        let mut text = String::new();
        for &c in &s.children {
            text.push_str(&all[c].text);
            text.push('\n');
        }
        let low = text.to_ascii_lowercase();
        if low.trim().is_empty() {
            return;
        }
        // a name handed over inside the body is given, not captured
        let given = |name: &str| {
            low.contains(&format!("give back {name}")) || low.contains(&format!("send {name}"))
        };
        let candidates: Vec<String> = self
            .top_defs
            .clone()
            .into_iter()
            .filter(|(name, mutable)| {
                !*mutable // Changeable is T0451's case
                    && !self.shared_names.iter().any(|n| n == name)
                    && self.defined_as_move_kind(name)
            })
            .map(|(name, _)| name)
            .collect();
        if candidates.is_empty() {
            return;
        }
        // the caret goes on the body sentence that reads the value, under the
        // name itself (the task sentence does not spell the value)
        for &c in &s.children {
            let child = &all[c];
            let lowered = child.text.to_ascii_lowercase();
            let words: Vec<&str> = lowered
                .split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
                .filter(|w| !w.is_empty())
                .collect();
            for name in &candidates {
                if !words.iter().any(|w| w.eq_ignore_ascii_case(name)) || given(name) {
                    continue;
                }
                let (lo, hi) = name_span(&child.text, name);
                self.err(
                    "T0450",
                    "Value crosses tasks unsafely.".to_string(),
                    child,
                    lo.min(child.text.len()),
                    hi.min(child.text.len()),
                    "A value that is not given, shared and immutable, guarded or atomic goes to another task.".to_string(),
                    "Give it, share it or guard it.".to_string(),
                );
                return;
            }
        }
    }

    /// M4-S2 / T0462 (the book's "Task outlives its block"): the name of a
    /// started task is the task's handle and belongs to the block. Returning
    /// it from the enclosing function, storing it in a collection or putting
    /// it into another name keeps it past the block; waiting for it inside
    /// the block is the allowed use.
    fn check_task_handle_escape(&mut self, name: &str, _s: &'a Sentence) {
        let mut escaped: Option<&'a Sentence> = None;
        for cand in self.all {
            if task_escape_shape(&cand.text, name) {
                escaped = Some(cand);
                break;
            }
        }
        if let Some(cand) = escaped {
            let (lo, hi) = name_span(&cand.text, name);
            self.err(
                "T0462",
                "Task outlives its block.".to_string(),
                cand,
                lo.min(cand.text.len()),
                hi.min(cand.text.len()),
                "A task name or a task handle is returned or stored outside its block.".to_string(),
                "Wait for it inside the block.".to_string(),
            );
        }
    }

    fn build_one(&mut self, s: &'a Sentence, sc: &mut Scope, env: &mut OwnEnv) -> Stmt {
        let toks = toks_of(&s.text);
        let first = first_word_lower(&s.text);
        match first.as_str() {
            "set" => self.parse_set(s, &toks, sc),
            // M4-S87 (7.12): Log LEVEL TEXT. - the level word comes
            // first (log is a reserved word, so no name starts a line
            // with it); the rest is raw text, parsed with the Say
            // machinery (names replaced as in Say, a secret as hidden,
            // a counter's value).
            "log" => {
                let level = match toks.get(1) {
                    Some(Token::Word { lower, .. }) => match LogLevel::from_word(lower) {
                        Some(l) => l,
                        None => {
                            self.err(
                                "T0113",
                                "A log sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "The level is the word debug, info, warning or error.".to_string(),
                                "Write Log info server started.".to_string(),
                            );
                            return Stmt::Note;
                        }
                    },
                    _ => {
                        self.err(
                            "T0113",
                            "A log sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The level is the word debug, info, warning or error.".to_string(),
                            "Write Log info server started.".to_string(),
                        );
                        return Stmt::Note;
                    }
                };
                match self.parse_say(toks[2..].to_vec(), Some(s), sc, false) {
                    Stmt::Say { expr, mods, lines } => Stmt::Log {
                        level,
                        expr,
                        mods,
                        lines,
                    },
                    _ => unreachable!("parse_say returns a Say"),
                }
            }
            "say" => self.parse_say(toks[1..].to_vec(), Some(s), sc, false),
            // ---- M4-10 (Appendix K 5.5/7.8) network ----
            "fetch" => self.parse_fetch(s, &toks, sc),
            "post" => self.parse_post(s, &toks, sc),
            "respond" => self.parse_respond(s, &toks, sc),
            "serve" => self.parse_serve(s, &toks, sc, env),
            "page" => self.parse_page(s, &toks),
            "be" => {
                // S62: Be careful. opens the block where the dangerous
                // sentences (the TLS skip) are legal.
                let ws: Vec<String> = s
                    .text
                    .to_ascii_lowercase()
                    .split_whitespace()
                    .map(|w| w.trim_end_matches('.').to_string())
                    .collect();
                if ws.len() == 2 && ws[1] == "careful" {
                    if s.children.is_empty() {
                        self.err(
                            "T0113",
                            "A Be careful block cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Be careful. needs its steps on indented lines under it.".to_string(),
                            "Indent the steps under Be careful.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    self.in_careful += 1;
                    let body = self.build_block(&s.children, sc, false, env);
                    self.in_careful -= 1;
                    Stmt::Careful { body }
                } else {
                    self.err(
                        "T0113",
                        "A sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "be starts only the Be careful block.".to_string(),
                        "Write Be careful. with its steps indented under it.".to_string(),
                    );
                    Stmt::Note
                }
            }
            "ask" => self.parse_ask(s, &toks, sc),
            "repeat" => self.parse_repeat(s, sc, env).unwrap_or(Stmt::Note),
            "for" => self.parse_for(s, sc, env).unwrap_or(Stmt::Note),
            "stop" => {
                // M4-G19: Stop task NAME. is the cancel request; a bare
                // Stop. stays the loop/block stop (M4's two words apart).
                let low = s.text.to_ascii_lowercase();
                let words: Vec<&str> = low.split_whitespace().collect();
                let words: Vec<&str> = words.iter().map(|w| w.trim_end_matches('.')).collect();
                if words.get(1) == Some(&"task") {
                    let name: String = words[2..].join(" ");
                    if name.is_empty() {
                        self.err(
                            "T0113",
                            "A task sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Stop task does not name a task.".to_string(),
                            "Write Stop task <name>.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    // Stopping a name that is not a task is the same
                    // confusion as waiting for one: T0168 wording on wait;
                    // Stop gets the sibling wording.
                    if !sc.find_task(&name) {
                        self.err(
                            "T0168",
                            "Stop task names a name that is not a task.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The name after Stop task is not a task.".to_string(),
                            "Start task <name>. first, or spell the task name right.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    return Stmt::StopTask { name };
                }
                Stmt::Stop
            }
            "skip" => Stmt::Skip,
            "combine" => self.parse_combine(s, &toks, sc),
            "apply" => self.parse_apply(s, &toks, sc),
            "add" => self.parse_add(s, &toks, sc),
            "hand" => self.parse_hand_back(s, &toks, sc),
            "requires" | "ensures" => {
                // T0161: a contract after a one-line function (the book's
                // "one-line To followed by Requires"); a stray contract
                // elsewhere is T0160. The loop sets prev_one_line_fn.
                self.parse_contract_stray(s, &toks, self.prev_one_line_fn)
            }
            "anything" => self.parse_interface_def(s, &toks),
            "by" => self.parse_default_def(s, &toks),
            "tagged" => self.parse_tagged(s),
            "put" => self.parse_put(s, &toks, sc),
            "remove" => {
                // M4-G41 (Appendix K 7.5): Remove file <ref>. /
                // Remove folder <ref>. - a plain value keeps the
                // Remove-from reading of M2.
                if matches!(
                    toks.get(1),
                    Some(Token::Word { lower, .. })
                        if lower == "file" || lower == "folder"
                ) {
                    match self.parse_file_ref_at(s, &toks, 1) {
                        Some(fr) => Stmt::RemovePath { file: fr },
                        None => Stmt::Note,
                    }
                } else {
                    self.parse_remove(s, &toks, sc)
                }
            }
            "look" => self.parse_look(s, &toks, sc, env),
            "when" => self.parse_when_file(s, &toks, sc, env),
            "a" | "an" => self.parse_type_decl(s, &toks, sc),
            "try" => Stmt::Note, // Try blocks are handled by build_block
            "fail" => self.parse_fail(Some(s), &toks, sc),
            "pass" => self.parse_pass(Some(s), &toks, sc),
            "close" => self.parse_close(Some(s), &toks, sc),
            "share" => self.parse_share(Some(s), &toks, sc),
            "use" => {
                // M4-G17 (Appendix K 7.3): Use NUMBER workers. sets the
                // Spread worker count. The module Use of chapter 36 reads
                // Use <module path>. - only words - so a leading whole
                // number selects the worker-count sentence.
                let is_workers = toks.len() >= 3
                    && matches!(&toks[1], Token::Whole { .. })
                    && matches!(
                        &toks[2],
                        Token::Word { lower, .. } if lower == "workers"
                    );
                if is_workers {
                    let n = match &toks[1] {
                        Token::Whole { value } => *value,
                        _ => unreachable!(),
                    };
                    // only the count and the word belong on the line
                    // (the token list may carry the period and/or an Eof)
                    let line_ok = toks
                        .iter()
                        .skip(3)
                        .all(|t| matches!(t, Token::Period | Token::Eof));
                    if !line_ok {
                        self.err(
                            "T0113",
                            "A worker sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Only the number and the word workers belong on the line.".to_string(),
                            "Write Use 4 workers.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    if n < 1 || n > 256 {
                        self.err(
                            "T0113",
                            "A worker sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "A worker count is a whole number from 1 to 256.".to_string(),
                            "Write Use 4 workers. (a number from 1 to 256).".to_string(),
                        );
                        return Stmt::Note;
                    }
                    return Stmt::UseWorkers { count: n as u64 };
                }
                // M4-G58 (Appendix K 7.7): Use seed N. sets the program's
                // random generator. A leading word seed selects the seed
                // sentence (a module path cannot start with the reserved
                // word seed - logged).
                let is_seed = toks.len() >= 3
                    && matches!(&toks[1], Token::Word { lower, .. } if lower == "seed")
                    && matches!(&toks[2], Token::Whole { .. });
                if is_seed {
                    let seed = match &toks[2] {
                        Token::Whole { value } => *value as u64,
                        _ => unreachable!(),
                    };
                    let line_ok = toks
                        .iter()
                        .skip(3)
                        .all(|t| matches!(t, Token::Period | Token::Eof));
                    if !line_ok {
                        self.err(
                            "T0113",
                            "A seed sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Only the word seed and a number belong on the line.".to_string(),
                            "Write Use seed 42.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    return Stmt::UseSeed { seed };
                }
                // M4-S88 (7.12): Use log level debug|info|warning|error.
                // sets the run's log level (the default is info: debug
                // lines are not written). The words log and level are
                // reserved, so a module path cannot start with them.
                let is_log_level = toks.len() >= 4
                    && matches!(&toks[1], Token::Word { lower, .. } if lower == "log")
                    && matches!(&toks[2], Token::Word { lower, .. } if lower == "level");
                if is_log_level {
                    let level = match toks.get(3) {
                        Some(Token::Word { lower, .. }) => match LogLevel::from_word(lower) {
                            Some(l) => l,
                            None => {
                                self.err(
                                    "T0113",
                                    "A log level sentence cannot be read.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    "The level is the word debug, info, warning or error."
                                        .to_string(),
                                    "Write Use log level debug.".to_string(),
                                );
                                return Stmt::Note;
                            }
                        },
                        _ => {
                            self.err(
                                "T0113",
                                "A log level sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "The level is the word debug, info, warning or error.".to_string(),
                                "Write Use log level debug.".to_string(),
                            );
                            return Stmt::Note;
                        }
                    };
                    let line_ok = toks
                        .iter()
                        .skip(4)
                        .all(|t| matches!(t, Token::Period | Token::Eof));
                    if !line_ok {
                        self.err(
                            "T0113",
                            "A log level sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Only the words log level and the level word belong on the line."
                                .to_string(),
                            "Write Use log level debug.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    return Stmt::LogLevel { level };
                }
                self.parse_use(Some(s), &toks)
            }
            // ---- M4 (Appendix K) pause-list sentences ----
            "wait" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1;
                if ts.peek_word() == Some("for") {
                    ts.pos += 1;
                    let mut name_words: Vec<String> = Vec::new();
                    loop {
                        let saved = ts.peek().cloned();
                        match saved {
                            Some(Token::Word { lower, .. }) => {
                                name_words.push(lower.to_ascii_lowercase());
                                ts.pos += 1;
                            }
                            _ => break,
                        }
                    }
                    let name: String = name_words.join(" ");
                    if name.is_empty() {
                        self.err(
                            "T0113",
                            "A task sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Wait for does not name a task.".to_string(),
                            "Write Wait for <task name>.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    if !sc.find_task(&name) {
                        // T0168: waiting on a name that is not a task
                        self.err(
                            "T0168",
                            "Wait for names a name that is not a task.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The name after Wait for is not a task.".to_string(),
                            "Start task <name>. first, or spell the task name right.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    Stmt::WaitFor { name }
                } else {
                    // a name that merely starts with "wait": parsed normally
                    self.parse_decl(s, toks, sc)
                }
            }
            "sleep" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1;
                if ts.peek_word() == Some("for") {
                    // M4-G4: Sleep for NUMBER <unit>. (M4-G5/G6)
                    ts.pos += 1;
                    let saved = ts.peek().cloned();
                    let amount: u64 = match saved {
                        Some(Token::Whole { value }) if value >= 0 => {
                            ts.pos += 1;
                            value as u64
                        }
                        _ => {
                            self.err("T0113", "A task sentence cannot be read.".to_string(), s, 0, s.text.len(),
                                "Sleep for needs a number of milliseconds, seconds, minutes, hours, days or weeks.".to_string(),
                                "Write Sleep for 2 seconds.".to_string());
                            return Stmt::Note;
                        }
                    };
                    let unit = ts
                        .peek_word()
                        .map(|w| w.to_ascii_lowercase())
                        .unwrap_or_default();
                    match unit.as_str() {
                        "milliseconds" | "seconds" | "minutes" | "hours" | "days" | "weeks" => {
                            ts.pos += 1;
                            Stmt::SleepFor { amount, unit }
                        }
                        _ => {
                            self.err("T0113", "A task sentence cannot be read.".to_string(), s, 0, s.text.len(),
                                "Sleep for needs a time unit.".to_string(),
                                "Write milliseconds, seconds, minutes, hours, days or weeks after the number.".to_string());
                            return Stmt::Note;
                        }
                    }
                } else {
                    self.parse_decl(s, toks, sc)
                }
            }
            // ---- M4 (Appendix K): Send VALUE to NAME. (G11) ------------
            "send" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1; // send
                let value_toks = ts.rest_until_word("to");
                // S73/S11: the value is the shown wording; a bare word
                // is text (value position), not an undefined name
                let value = self.value_position_expr(value_toks, Some(s), sc);
                ts.pos += 1; // to
                let mut name_words: Vec<String> = Vec::new();
                loop {
                    match ts.peek().cloned() {
                        Some(Token::Word { lower, .. }) => {
                            name_words.push(lower.to_ascii_lowercase());
                            ts.pos += 1;
                        }
                        _ => break,
                    }
                }
                let name: String = name_words.join(" ");
                if name.is_empty() {
                    self.err(
                        "T0113",
                        "A channel sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Send does not name a channel.".to_string(),
                        "Write Send <value> to <channel name>.".to_string(),
                    );
                    return Stmt::Note;
                }
                // M4-S73/D13: a Send names a channel, or a connection
                // value (the provided connection inside a live block, or
                // a stored connection). An unknown element kind (list of
                // nothing) is checked at run time; everything else is
                // the T0168 wording (deviation logged: the reuse).
                let def_kind = sc.find(&name).map(|d| d.kind);
                if matches!(
                    def_kind,
                    Some(Kind::Channel(_)) | Some(Kind::Connection) | Some(Kind::Unknown)
                ) {
                    return Stmt::Send { value, name };
                }
                if self.in_live > 0 && name == "connection" {
                    return Stmt::WsSend { value };
                }
                // T0169 (M4-G11): a Send to a name that is not a channel
                // is a channel kind mismatch
                let (lo, hi) = span_of(&s.text, &name);
                self.err(
                    "T0169",
                    "Channel kind mismatch.".to_string(),
                    s,
                    lo,
                    hi,
                    "A value of the wrong kind is sent.".to_string(),
                    "Send the channel's kind.".to_string(),
                );
                return Stmt::Note;
            }
            // ---- M4 (Appendix K): Receive from NAME. (G12) ------------
            "receive" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1; // receive
                if ts.peek_word() == Some("from") {
                    ts.pos += 1;
                    let mut name_words: Vec<String> = Vec::new();
                    loop {
                        match ts.peek().cloned() {
                            Some(Token::Word { lower, .. }) => {
                                name_words.push(lower.to_ascii_lowercase());
                                ts.pos += 1;
                            }
                            _ => break,
                        }
                    }
                    let name: String = name_words.join(" ");
                    if name.is_empty() {
                        self.err(
                            "T0113",
                            "A channel sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Receive from does not name a channel.".to_string(),
                            "Write Receive from <channel name>.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    // M4-S73: Receive from connection. in a live block
                    // reads one text frame; it gives maybe text (missing
                    // when the other side closed). A name of the
                    // connection kind (a stored connection, M4-D13)
                    // reads from that connection; an unknown element kind
                    // (list of nothing) is checked at run time.
                    let def_kind = sc.find(&name).map(|d| d.kind);
                    if matches!(
                        def_kind,
                        Some(Kind::Channel(_)) | Some(Kind::Connection) | Some(Kind::Unknown)
                    ) {
                        return Stmt::Receive { name };
                    }
                    if self.in_live > 0 && name == "connection" {
                        return Stmt::WsRecv;
                    }
                    self.err(
                        "T0168",
                        "Receive names a name that is not a channel.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "The name after Receive from is not a channel.".to_string(),
                        "Define <name> as channel of <kind> first.".to_string(),
                    );
                    return Stmt::Note;
                } else {
                    // a name that merely starts with receive: parsed normally
                    self.parse_decl(s, toks, sc)
                }
            }
            // ---- M4-8 (Appendix K 7.10): Run and Exit -----------------
            "run" => {
                // M4-G20: Run NAME [with operand (and operand)*]. The
                // program is found on the path (T0171 for a name with a
                // path, M4-S76); each operand is one argument; no shell.
                let mut ts = TS::new(&toks);
                ts.pos += 1; // run
                let Some(prog_name) = ts.peek_word().map(|w| w.to_string()) else {
                    self.err(
                        "T0113",
                        "A Run sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Run does not name a program.".to_string(),
                        "Write Run echo with hello.".to_string(),
                    );
                    return Stmt::Note;
                };
                ts.pos += 1;
                // the name is one word of letters and digits; a symbol
                // inside it (m48_helper) stops the tokens early and the
                // sentence would read as a shorter name - refuse instead
                if Lexer::new(&s.text).tokenize().1.is_some() {
                    self.err("T0113", "A Run sentence cannot be read.".to_string(), s, 0, s.text.len(),
                        "The name after Run is one word of letters and digits; the line stops there.".to_string(),
                        "Write Run <name> with <arguments>. The program is found on the path without an ending.".to_string());
                    return Stmt::Note;
                }
                if !lykaon_core::args::valid_prog_name(&prog_name) {
                    // S76's own refusal row: the program is found on the
                    // path, so its name carries no path
                    self.err(
                        "T0171",
                        "A Run name carries a path.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "The name after Run is found on the path; it is not a path.".to_string(),
                        "Write Run <program name> with <arguments>.".to_string(),
                    );
                    return Stmt::Note;
                }
                // The name is one word. A dotted spelling (tool.bat) lexes
                // as the word, a period and the rest; the leftovers are
                // refused, not ignored.
                if ts.peek() == Some(&Token::Period)
                    && !matches!(ts.toks.get(ts.pos + 1), Some(Token::Eof) | None)
                {
                    self.err("T0113", "A Run sentence cannot be read.".to_string(), s, 0, s.text.len(),
                        "The name after Run is one word; the line does not end there.".to_string(),
                        "Write Run <name> with <arguments>. The program is found on the path without an ending.".to_string());
                    return Stmt::Note;
                }
                let mut args: Vec<Expr> = Vec::new();
                if ts.consume_word("with") {
                    loop {
                        let arg_toks = ts.rest_until_word("and");
                        if arg_toks.is_empty() {
                            self.err(
                                "T0113",
                                "A Run sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "Run with expects an argument between the and words.".to_string(),
                                "Write Run echo with hello and hi.".to_string(),
                            );
                            return Stmt::Note;
                        }
                        args.push(self.parse_expr(arg_toks, Some(s), sc, false));
                        if !ts.consume_word("and") {
                            break;
                        }
                    }
                }
                if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
                    self.err(
                        "T0113",
                        "A Run sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "The arguments of Run are joined by and; the line ends there.".to_string(),
                        "Write Run echo with hello and hi.".to_string(),
                    );
                    return Stmt::Note;
                }
                Stmt::RunProc {
                    name: prog_name,
                    args,
                }
            }
            "exit" => {
                // M4-G21: Exit with NUMBER. The code is 0 to 255 (M4-S78);
                // the range is a compile check like Use N workers (T0113).
                let mut ts = TS::new(&toks);
                ts.pos += 1; // exit
                if !ts.consume_word("with") {
                    self.err(
                        "T0113",
                        "An Exit sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Exit names its code with with.".to_string(),
                        "Write Exit with 0.".to_string(),
                    );
                    return Stmt::Note;
                }
                let code = match ts.peek().cloned() {
                    Some(Token::Whole { value }) => {
                        ts.pos += 1;
                        value
                    }
                    Some(Token::Negative { value }) => {
                        ts.pos += 1;
                        -value
                    }
                    _ => {
                        self.err(
                            "T0113",
                            "An Exit sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The code of Exit is a number.".to_string(),
                            "Write Exit with 0.".to_string(),
                        );
                        return Stmt::Note;
                    }
                };
                if !(0..=255).contains(&code) {
                    self.err(
                        "T0113",
                        "An Exit sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "An exit code is a number from 0 to 255.".to_string(),
                        "Write Exit with 0.".to_string(),
                    );
                    return Stmt::Note;
                }
                if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
                    self.err(
                        "T0113",
                        "An Exit sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Only the code belongs after with; the line ends there.".to_string(),
                        "Write Exit with 0.".to_string(),
                    );
                    return Stmt::Note;
                }
                Stmt::Exit { code }
            }
            "check" => self.parse_check(Some(s), &toks, sc),
            "pretend" => self.parse_pretend(Some(s), &toks, sc),
            // ---- M4-5 (Appendix K 7.5) file and folder sentences ------
            "read" => {
                let mut ts = TS::new(&toks);
                ts.pos += 1; // read
                // ---- M4-6 (Appendix K 7.6): Read json file F as T. /
                // Read json from text as T. - same wording for toml,
                // yaml, xml, csv (M4-G53 format_word).
                if let Some(format) = FORMAT_WORD(ts.peek_word()) {
                    ts.pos += 1;
                    return self.parse_format_read(format, &mut ts, s, sc, &toks);
                }
                if ts.peek_word() == Some("bytes") {
                    ts.pos += 1;
                    if !ts.consume_word("of")
                        || !matches!(ts.peek_word(), Some("file") | Some("folder"))
                    {
                        self.err(
                            "T0113",
                            "A file sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Read bytes of expects file <name> after it.".to_string(),
                            "Write Read bytes of file <name>.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    return match self.parse_file_ref(&mut ts, s, None) {
                        Some(fr) => Stmt::ReadBytes { file: fr },
                        None => Stmt::Note,
                    };
                }
                if matches!(ts.peek_word(), Some("file") | Some("folder")) {
                    return match self.parse_file_ref(&mut ts, s, None) {
                        Some(fr) => Stmt::ReadFile { file: fr },
                        None => Stmt::Note,
                    };
                }
                self.parse_decl(s, toks, sc)
            }
            "write" => match self.parse_file_write(&toks, s, sc) {
                Some(st) => st,
                None => self.parse_decl(s, toks, sc),
            },
            "append" => match self.parse_file_write(&toks, s, sc) {
                Some(st) => st,
                None => self.parse_decl(s, toks, sc),
            },
            "replace" => {
                let mut ts = TS::new(&toks);
                if matches!(ts.peek_next(), Some("file") | Some("folder")) {
                    ts.pos += 1; // replace
                    return match self.parse_file_ref(&mut ts, s, None) {
                        Some(fr) => {
                            if !ts.consume_word("with") {
                                self.err(
                                    "T0113",
                                    "A file sentence cannot be read.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    "Replace file writes `with` before the new content."
                                        .to_string(),
                                    "Write Replace file <name> with <text>.".to_string(),
                                );
                                return Stmt::Note;
                            }
                            let value =
                                self.value_position_expr(ts.rest_without_period(), Some(s), sc);
                            Stmt::ReplaceFile { file: fr, value }
                        }
                        None => Stmt::Note,
                    };
                }
                self.parse_decl(s, toks, sc)
            }
            "save" => {
                // M4-6: Save <value> as json to file F. (the format word
                // also toml, yaml, xml, csv). Save is a files-chapter
                // shape here; a `Save` that holds no as-format falls
                // back to the old readings (none yet - a plain save is
                // a shape error).
                let mut ts = TS::new(&toks);
                ts.pos += 1; // save
                let holds_as_format = {
                    let mut idx = ts.pos;
                    let mut found = false;
                    while idx + 1 < toks.len() {
                        if let (Token::Word { lower: l1, .. }, Token::Word { lower: l2, .. }) =
                            (&toks[idx], &toks[idx + 1])
                        {
                            if l1 == "as" && FORMAT_WORD(Some(l2)).is_some() {
                                found = true;
                                break;
                            }
                        }
                        idx += 1;
                    }
                    found
                };
                if holds_as_format {
                    return self.parse_format_save(&mut ts, s, sc, &toks);
                }
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "Save expects as <format> and to file after the value.".to_string(),
                    "Write Save <value> as json to file <name>.".to_string(),
                );
                Stmt::Note
            }
            "make" => {
                // M4-G40/G46: Make folder <ref>. / Make temporary file
                // <name>. - anything else keeps the old reading.
                if matches!(
                    (toks.get(1), toks.get(2)),
                    (Some(Token::Word { lower, .. }), Some(Token::Word { .. }))
                        if lower == "folder"
                ) {
                    let mut ts = TS::new(&toks);
                    ts.pos += 1; // make
                    return match self.parse_file_ref(&mut ts, s, None) {
                        Some(fr) => Stmt::MakeFolder { file: fr },
                        None => Stmt::Note,
                    };
                }
                if matches!(
                    (toks.get(1), toks.get(2)),
                    (
                        Some(Token::Word { lower: l1, .. }),
                        Some(Token::Word { lower: l2, .. })
                    ) if l1 == "temporary" && l2 == "file"
                ) {
                    let mut name_words: Vec<String> = Vec::new();
                    for t in toks.iter().skip(3) {
                        match t {
                            Token::Word { lower, .. } => name_words.push(lower.clone()),
                            Token::Whole { value } => name_words.push(value.to_string()),
                            Token::Period | Token::Eof => {}
                            _ => {
                                name_words.clear();
                                break;
                            }
                        }
                    }
                    let name = name_words.join(" ");
                    if name.is_empty()
                        || name.split(' ').any(|w| {
                            matches!(w, "file" | "folder" | "with" | "in" | "on" | "changes")
                        })
                    {
                        self.err(
                            "T0113",
                            "A file sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "Make temporary file writes only a plain name on the line.".to_string(),
                            "Write Make temporary file data.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    if sc.find(&name).is_some() {
                        self.err(
                            "T0207",
                            format!("{name} is defined twice."),
                            s,
                            0,
                            s.text.len(),
                            "A name is defined again where it is already visible.".to_string(),
                            "Give the file a new name.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    // the path binds NAME as a text value; the file is
                    // removed when the block ends (M4-S38)
                    sc.define(
                        &name,
                        Def {
                            kind: Kind::Text,
                            mutable: false,
                            shared: false,
                        },
                    );
                    self.temp_names.push(name.clone());
                    return Stmt::MakeTempFile { name };
                }
                self.parse_decl(s, toks, sc)
            }
            "move" => {
                // M4-G42: Move file <ref> to file <ref2>.
                let mut ts = TS::new(&toks);
                if matches!(ts.peek_next(), Some("file") | Some("folder")) {
                    ts.pos += 1;
                    return self.parse_file_pair(&mut ts, s, "to");
                }
                self.parse_decl(s, toks, sc)
            }
            "duplicate" => {
                // M4-G43: Duplicate file <ref> as file <ref2>.
                let mut ts = TS::new(&toks);
                if matches!(ts.peek_next(), Some("file") | Some("folder")) {
                    ts.pos += 1;
                    return self.parse_file_pair(&mut ts, s, "as");
                }
                self.parse_decl(s, toks, sc)
            }
            "list" => {
                // M4-G44: List files in folder <F>. - names that merely
                // start with list keep the old reading.
                let mut ts = TS::new(&toks);
                ts.pos += 1; // list
                if ts.peek_word() == Some("files") && ts.peek_next() == Some("in") {
                    ts.pos += 2;
                    return match self.parse_file_ref(&mut ts, s, None) {
                        Some(fr) => Stmt::ListFolder { file: fr },
                        None => Stmt::Note,
                    };
                }
                self.parse_decl(s, toks, sc)
            }
            "zip" | "unzip" | "gzip" => match self.parse_zip(&toks, s) {
                Some(st) => st,
                None => self.parse_decl(s, toks, sc),
            },
            _ => self.parse_decl(s, toks, sc),
        }
    }

    /// Anything that can speak must have speak. (ch.23, M3-G7): an interface.
    fn parse_interface_def(&mut self, s: &'a Sentence, toks: &[Token]) -> Stmt {
        let mut ts = TS::new(toks);
        ts.consume_word("anything");
        if !ts.consume_word("that") {
            return Stmt::Note;
        }
        ts.consume_word("can");
        let Some(verb) = ts.peek_word().map(|w| w.to_ascii_lowercase()) else {
            return Stmt::Note;
        };
        ts.pos += 1;
        if !ts.consume_word("must") || !ts.consume_word("have") {
            self.err(
                "T0113",
                "An interface sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The sentence starts with anything but is not an interface.".to_string(),
                "Write Anything that can <verb> must have <function>.".to_string(),
            );
            return Stmt::Note;
        }
        let fn_name = ts.peek_word().unwrap_or(&verb).to_ascii_lowercase();
        // An interface hoisted before the walk is not declared twice.
        if self
            .interfaces
            .iter()
            .any(|i| i.verb == verb && i.fn_name == fn_name)
        {
            return Stmt::Note;
        }
        self.interfaces.push(Interface {
            verb: verb.clone(),
            fn_name,
            default: None,
        });
        // the verb becomes a defined word (the agent noun kind, M3-D11), and
        // the interface name itself is reserved (ch.23)
        Stmt::Note
    }

    /// By default speak says nothing. (ch.23, M3-G8): a default for an
    /// interface. A default with no interface is T0159.
    fn parse_default_def(&mut self, s: &'a Sentence, toks: &[Token]) -> Stmt {
        let mut ts = TS::new(toks);
        ts.consume_word("by");
        if !ts.consume_word("default") {
            return Stmt::Note;
        }
        let fn_name = ts.peek_word().unwrap_or("").to_ascii_lowercase();
        ts.pos += 1;
        ts.consume_word("says");
        let rest = ts
            .rest_without_period()
            .iter()
            .filter_map(|t| w_lower(t).cloned())
            .collect::<Vec<_>>()
            .join(" ");
        let text = if rest == "nothing" {
            String::new()
        } else {
            s.text
                .split_whitespace()
                .skip_while(|w| !w.eq_ignore_ascii_case("says"))
                .skip(1)
                .collect::<Vec<_>>()
                .join(" ")
                .trim_end_matches('.')
                .trim_matches('"')
                .to_string()
        };
        match self.interfaces.last_mut() {
            Some(i) if i.fn_name == fn_name => {
                i.default = Some(text);
            }
            Some(_) | None => {
                self.err(
                    "T0159",
                    "Default without interface.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "By default has no interface above it.".to_string(),
                    "Declare the interface first.".to_string(),
                );
            }
        }
        Stmt::Note
    }

    /// Tagged <name>. (M3-S39): labels the next definition.
    fn parse_tagged(&mut self, s: &'a Sentence) -> Stmt {
        let name = s
            .text
            .split_whitespace()
            .nth(1)
            .unwrap_or("")
            .trim_end_matches('.')
            .to_ascii_lowercase();
        if !name.is_empty() {
            self.pending_tags.push(name);
        }
        Stmt::Note
    }

    /// Hand back <value>. inside a generator function (ch.25, M3-S30).
    fn parse_hand_back(&mut self, s: &'a Sentence, toks: &[Token], _sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // hand
        ts.consume_word("back");
        self.text_depth += 1;
        let e = self.parse_expr(ts.rest_without_period(), Some(s), _sc, false);
        self.text_depth -= 1;
        Stmt::HandBack(e)
    }

    /// A Requires/Ensures outside a function top (T0160): parsed so the span
    /// can be pinpointed, then reported.
    fn parse_contract_stray(
        &mut self,
        s: &'a Sentence,
        toks: &[Token],
        prev_one_line: bool,
    ) -> Stmt {
        // T0161: the contract belongs to a one-line function - use a block
        let (code, what, why, fix) = if prev_one_line {
            (
                "T0161",
                "Contract in a one-line function.",
                "A one-line function has a contract.",
                "Use a block function.",
            )
        } else {
            (
                "T0160",
                "Contract not first.",
                "Requires or Ensures is not at the top of the block.",
                "Move it up.",
            )
        };
        self.err(
            code,
            what.to_string(),
            s,
            0,
            s.text.len(),
            why.to_string(),
            fix.to_string(),
        );
        let mut ts = TS::new(toks);
        ts.pos += 1;
        ts.consume_word("checked");
        let _ = self.parse_condition(ts.rest_without_period(), Some(s), &Scope::default());
        Stmt::Note
    }

    /// Combine <list> with <word>. folds the list to one value (Ch.16).
    fn parse_combine(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // combine
        let list_toks = ts.rest_until_word("with");
        let list = self.parse_expr(list_toks, Some(s), sc, false);
        ts.pos += 1; // with
        let word = match ts.peek_word() {
            Some(w) => w.to_string(),
            None => String::new(),
        };
        Stmt::Evaluate {
            expr: Expr {
                kind: Kind::Unknown,
                e: E::Combine {
                    list: Box::new(list),
                    word,
                },
                dis: s.text.clone(),
                can_fail: false,
                num_word: false,
            },
            list: false,
        }
    }

    /// Apply <fn> to each of <list>. maps the list (Ch.16).
    fn parse_apply(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // apply
        let name = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => String::new(),
        };
        ts.pos += 1;
        while ts.peek_word() == Some("to") || ts.peek_word() == Some("each") {
            ts.pos += 1;
        }
        ts.consume_word("of");
        let list_toks = ts.rest_without_period();
        let list = self.parse_expr(list_toks, Some(s), sc, false);
        Stmt::Evaluate {
            expr: Expr {
                kind: Kind::Unknown,
                e: E::ApplyEach {
                    name,
                    list: Box::new(list),
                },
                dis: s.text.clone(),
                can_fail: false,
                num_word: false,
            },
            list: true,
        }
    }

    /// Add <value> to <list>. (Ch.76)
    fn parse_add(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // add
        let value_toks = ts.rest_until_word("to");
        let value = self.parse_expr(value_toks, Some(s), sc, false);
        ts.pos += 1; // to
        let list = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => String::new(),
        };
        ts.pos += 1; // the target name word
        // M4-G13: Add V to NAME atomically. - one machine step (M4-S19)
        if ts.peek_word() == Some("atomically") {
            ts.pos += 1;
            return Stmt::AtomicAdd { value, name: list };
        }
        // M4-S20: on a counter, "Add V to hits." adds (one sentence, one
        // whole-number step). Every other target keeps the list-append
        // reading (the runtime falls through to the counter add anyway).
        let is_counter = sc
            .find(&list)
            .map(|d| matches!(d.kind, Kind::Counter))
            .unwrap_or(false);
        if is_counter {
            return Stmt::AtomicAdd { value, name: list };
        }
        Stmt::Append { value, list }
    }

    /// Put <value> in <map> under <key>. (M2)
    // ---- M4-5 (Appendix K 7.5) file reference parsing -----------------

    /// M4-G28 file_ref / M4-G33 folder_ref. The words:
    /// `file <NAME words>...` or `folder <NAME words>...`, with optional
    /// `with extension <word>` (M4-S32), repeated `in folder <NAME>`
    /// steps, and an optional root (`in parent folder`, `in home folder`,
    /// `in current folder`, `in temporary folder`, `in root folder`,
    /// M4-S30; `on drive <name>` is read on systems with drives, a fatal
    /// T0171 elsewhere). `file named <words>` is a raw path, terminal per
    /// the grammar (M4-S29). The ref is read with the verb consumed or a
    /// position given; `stop` ends NAME collection for sentences with a
    /// trailing word (When ... changes.).
    fn parse_file_ref(
        &mut self,
        ts: &mut TS,
        s: &'a Sentence,
        stop: Option<&str>,
    ) -> Option<FileRef> {
        let toks = ts.toks;
        let word_at = |i: usize| -> Option<&str> {
            toks.get(i).and_then(|t| match t {
                Token::Word { lower, .. } => Some(lower.as_str()),
                _ => None,
            })
        };
        // first word: file or folder (folder ref => the folder reading)
        let folder = match ts.peek_word() {
            Some("folder") => {
                ts.pos += 1;
                true
            }
            Some("file") => {
                ts.pos += 1;
                false
            }
            _ => {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A file sentence expects file or folder next.".to_string(),
                    "Write file <name>. or folder <name>.".to_string(),
                );
                return None;
            }
        };
        // file named ... : the raw path as written, terminal for the line
        if ts.peek_word() == Some("named") {
            ts.pos += 1;
            let mut words: Vec<String> = Vec::new();
            loop {
                match ts.peek() {
                    Some(Token::Word { text, lower, .. }) => {
                        if stop == Some(lower.as_str()) {
                            break;
                        }
                        words.push(text.clone());
                    }
                    Some(Token::Whole { value }) => words.push(value.to_string()),
                    Some(Token::Period) | Some(Token::Eof) | None => break,
                    _ => break,
                }
                ts.pos += 1;
            }
            if words.is_empty() {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "file named writes path words after named.".to_string(),
                    "Write file named notes txt.".to_string(),
                );
                return None;
            }
            return Some(FileRef {
                folder,
                raw: Some(words.join(" ")),
                temp: None,
                name: String::new(),
                ext: None,
                folders: Vec::new(),
                root: None,
            });
        }
        // the NAME words, up to the next reserved step (or the stop word)
        let mut name_words: Vec<String> = Vec::new();
        loop {
            if stop.is_some() && ts.peek_word() == stop {
                break;
            }
            let reserved = ts.peek_word().map(|w| {
                matches!(
                    (w, word_at(ts.pos + 1)),
                    ("with", Some("extension"))
                        | (
                            "in",
                            Some("folder" | "parent" | "home" | "current" | "temporary" | "root")
                        )
                        | ("on", Some("drive"))
                )
            });
            match ts.peek() {
                Some(Token::Period) | Some(Token::Eof) | None => break,
                _ if reserved == Some(true) => break,
                Some(Token::Word { lower, .. }) => name_words.push(lower.clone()),
                Some(Token::Whole { value }) => name_words.push(value.to_string()),
                _ => {
                    self.err(
                        "T0113",
                        "A file sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "A file or folder name is plain words.".to_string(),
                        "Write file <name words>. or file named <path words>.".to_string(),
                    );
                    return None;
                }
            }
            ts.pos += 1;
        }
        if name_words.is_empty() {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The sentence does not name a file or a folder.".to_string(),
                "Write file report. or folder output.".to_string(),
            );
            return None;
        }
        let name = name_words.join(" ");
        // M4-G46: a name bound by Make temporary file wins (the choice is
        // logged); an unbound reference reads literally (runtime fallback)
        let temp = if self.temp_names.iter().any(|n| *n == name) {
            Some(name.clone())
        } else {
            None
        };
        let mut ext: Option<String> = None;
        let mut folders: Vec<String> = Vec::new();
        let mut root: Option<FileRoot> = None;
        loop {
            if ts.peek_word() == Some("with") && word_at(ts.pos + 1) == Some("extension") {
                ts.pos += 2;
                let word = match ts.peek() {
                    Some(Token::Word { lower, .. }) => lower.clone(),
                    Some(Token::Whole { value }) => value.to_string(),
                    _ => String::new(),
                };
                ts.pos += 1;
                if word.is_empty() {
                    self.err(
                        "T0113",
                        "A file sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "with extension writes the extension's word.".to_string(),
                        "Write with extension json.".to_string(),
                    );
                    return None;
                }
                ext = Some(word);
                continue;
            }
            if ts.peek_word() == Some("in") && word_at(ts.pos + 1) == Some("folder") {
                ts.pos += 2;
                let word = match ts.peek() {
                    Some(Token::Word { lower, .. }) => lower.clone(),
                    Some(Token::Whole { value }) => value.to_string(),
                    _ => String::new(),
                };
                ts.pos += 1;
                if word.is_empty() {
                    self.err(
                        "T0113",
                        "A file sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "in folder writes the folder's word.".to_string(),
                        "Write in folder output.".to_string(),
                    );
                    return None;
                }
                folders.push(word);
                continue;
            }
            if ts.peek_word() == Some("in") {
                let root_word = word_at(ts.pos + 1).unwrap_or("");
                if matches!(
                    root_word,
                    "parent" | "home" | "current" | "temporary" | "root"
                ) && word_at(ts.pos + 2) == Some("folder")
                {
                    ts.pos += 3;
                    root = Some(match root_word {
                        "parent" => FileRoot::Parent,
                        "home" => FileRoot::Home,
                        "current" => FileRoot::Current,
                        "temporary" => FileRoot::Temporary,
                        _ => FileRoot::Root,
                    });
                    continue;
                }
            }
            if ts.peek_word() == Some("on") && word_at(ts.pos + 1) == Some("drive") {
                ts.pos += 2;
                let word = match ts.peek() {
                    Some(Token::Word { lower, .. }) => lower.clone(),
                    Some(Token::Whole { value }) => value.to_string(),
                    _ => String::new(),
                };
                ts.pos += 1;
                if word.is_empty() {
                    self.err(
                        "T0113",
                        "A file sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "on drive writes the drive's word.".to_string(),
                        "Write on drive C.".to_string(),
                    );
                    return None;
                }
                root = Some(FileRoot::Drive(word));
                continue;
            }
            break;
        }
        Some(FileRef {
            folder,
            raw: None,
            temp,
            name,
            ext,
            folders,
            root,
        })
    }

    /// The same reference read from a token list at a position (the verb
    /// is already consumed by the caller when `at` points past it, or at
    /// the verb when the ref starts at `file`/`folder`).
    fn parse_file_ref_at(&mut self, s: &'a Sentence, toks: &[Token], at: usize) -> Option<FileRef> {
        let mut ts = TS::new(toks);
        ts.pos = at;
        self.parse_file_ref(&mut ts, s, None)
    }

    /// M4-G36: Write <value> to file <ref>. (M4-G37 reads Append the same
    /// way.) `None` means the sentence was not a file sentence (the
    /// caller keeps the old reading of a name that starts with the verb).
    fn parse_file_write(
        &mut self,
        toks: &[Token],
        s: &'a Sentence,
        sc: &mut Scope,
    ) -> Option<Stmt> {
        let mut ts = TS::new(toks);
        ts.pos += 1; // write / append
        // M4-G36/G37: the value is the words between the verb and the `to`
        // that starts the file reference (`to file ...` / `to folder ...`),
        // in the value position of Ch.4. The ref itself may carry folder
        // steps with their own plain words, so the pair is scanned for.
        fn word_at(t: &Token) -> Option<&str> {
            match t {
                Token::Word { lower, .. } => Some(lower.as_str()),
                _ => None,
            }
        }
        let mut to_at: Option<usize> = None;
        let mut i = ts.pos;
        while i + 1 < ts.toks.len() {
            if word_at(&ts.toks[i]) == Some("to")
                && matches!(word_at(&ts.toks[i + 1]), Some("file") | Some("folder"))
            {
                to_at = Some(i);
                break;
            }
            i += 1;
        }
        let Some(fa) = to_at else {
            return None;
        };
        let value_toks = ts.toks[ts.pos..fa].to_vec();
        if value_toks.is_empty() {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The sentence writes nothing to the file.".to_string(),
                "Write <value> to file <name>.".to_string(),
            );
            return Some(Stmt::Note);
        }
        let value = self.value_position_expr(value_toks, Some(s), sc);
        ts.pos = fa + 1; // past `to`
        let is_append = matches!(
            toks.first(),
            Some(Token::Word { lower, .. }) if lower == "append"
        );
        match self.parse_file_ref(&mut ts, s, None) {
            Some(fr) => {
                if is_append {
                    Some(Stmt::AppendFile { file: fr, value })
                } else {
                    Some(Stmt::WriteFile { file: fr, value })
                }
            }
            None => {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "This is not a file sentence this program can read.".to_string(),
                    "Write <value> to file <name>.".to_string(),
                );
                Some(Stmt::Note)
            }
        }
    }

    /// M4-G42/G43: two file refs separated by `to` (a move) or `as` (a
    /// duplicate). A folder on the left duplicates recursively (logged).
    fn parse_file_pair(&mut self, ts: &mut TS, s: &'a Sentence, middle: &str) -> Stmt {
        let Some(from) = self.parse_file_ref(ts, s, None) else {
            return Stmt::Note;
        };
        if !ts.consume_word(middle) {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                format!("The sentence does not say {middle} between the two file references."),
                format!("Write file <name> {middle} file <other name>."),
            );
            return Stmt::Note;
        }
        let Some(to) = self.parse_file_ref(ts, s, None) else {
            return Stmt::Note;
        };
        if middle == "as" {
            Stmt::DuplicatePath { from, to }
        } else {
            Stmt::MovePath { from, to }
        }
    }

    /// M4-G48: Zip folder <ref> to file <ref>. / Unzip file <ref> to
    /// folder <ref>. / Gzip file <ref> to file <ref>. `None` keeps the
    /// old reading for names that merely start with the verb.
    fn parse_zip(&mut self, toks: &[Token], s: &'a Sentence) -> Option<Stmt> {
        let mut ts = TS::new(toks);
        let op = match ts.peek_word() {
            Some("zip") => ZipKind::Zip,
            Some("unzip") => ZipKind::Unzip,
            Some("gzip") => ZipKind::Gzip,
            _ => return None,
        };
        ts.pos += 1;
        if !matches!(ts.peek_word(), Some("file") | Some("folder")) {
            return None;
        }
        let Some(from) = self.parse_file_ref(&mut ts, s, None) else {
            return Some(Stmt::Note);
        };
        if !ts.consume_word("to") {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The sentence does not say to between the two references.".to_string(),
                "Write Zip folder <name> to file <other>.".to_string(),
            );
            return Some(Stmt::Note);
        }
        let Some(to) = self.parse_file_ref(&mut ts, s, None) else {
            return Some(Stmt::Note);
        };
        Some(Stmt::ZipOp { op, from, to })
    }

    /// M4-6 (Appendix K 7.6): the read side of the formats,
    /// `Read <fw> file <ref> as T.` (M4-G53 fw = json/toml/yaml/xml/csv)
    /// and `Read <fw> from text as T.` The decoded value lands in it.
    fn parse_format_read(
        &mut self,
        format: &'static str,
        ts: &mut TS,
        s: &'a Sentence,
        sc: &mut Scope,
        toks: &[Token],
    ) -> Stmt {
        if matches!(ts.peek_word(), Some("file") | Some("folder")) {
            // M4-S42: the file reference reads with `as` as its stop word
            // (the type words follow it)
            let fr = match self.parse_file_ref(ts, s, Some("as")) {
                Some(fr) => fr,
                None => return Stmt::Note,
            };
            if !ts.consume_word("as") {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A format read expects as <kind> after the file reference.".to_string(),
                    "Write Read json file <name> as <kind>.".to_string(),
                );
                return Stmt::Note;
            }
            let target = self.parse_format_target(ts, s);
            self.check_format_target(format, &target, s);
            Stmt::ReadFormat {
                format: format.to_string(),
                file: fr,
                target,
            }
        } else if ts.consume_word("from") {
            if !ts.consume_word("text") {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A format read takes file <name> or from text.".to_string(),
                    "Write Read json from text as <kind>.".to_string(),
                );
                return Stmt::Note;
            }
            // the decode source is the words between `text` and `as`
            let start = ts.pos;
            let mut end = None;
            for (idx, t) in toks.iter().enumerate().skip(start) {
                if matches!(t, Token::Word { lower, .. } if lower == "as") {
                    end = Some(idx);
                    break;
                }
            }
            let Some(end) = end else {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A format read from text expects as <kind> after the text.".to_string(),
                    "Write Read json from text as <kind>.".to_string(),
                );
                return Stmt::Note;
            };
            let value = self.value_position_expr(toks[start..end].to_vec(), Some(s), sc);
            ts.pos = end;
            ts.pos += 1; // as
            let target = self.parse_format_target(ts, s);
            self.check_format_target(format, &target, s);
            Stmt::ReadFormatText {
                format: format.to_string(),
                value,
                target,
            }
        } else {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "A format read takes file <name> or from text after the format word.".to_string(),
                "Write Read json file <name> as <kind>.".to_string(),
            );
            Stmt::Note
        }
    }

    /// The T after `as`: a kind name, then the collection type words
    /// (S42). A missing kind is a shape error.
    fn parse_format_target(&mut self, ts: &mut TS, s: &'a Sentence) -> Kind {
        match self.format_type_word(ts) {
            Some(k) => k,
            None => {
                self.err(
                    "T0113",
                    "A file sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The read needs a kind name after as.".to_string(),
                    "Write Read json file <name> as <kind>.".to_string(),
                );
                Kind::Unknown
            }
        }
    }

    /// M4-6: `Save <value> as <fw> to file <ref>.` The value is the
    /// words between Save and `as` (the value position of Ch.4); the
    /// format word carries the encoding, and the file reference reads
    /// to the end of the sentence.
    fn parse_format_save(
        &mut self,
        ts: &mut TS,
        s: &'a Sentence,
        sc: &mut Scope,
        toks: &[Token],
    ) -> Stmt {
        // scan for `as <format word>`
        let mut as_at = None;
        let mut format: Option<&'static str> = None;
        let mut idx = ts.pos;
        while idx + 1 < toks.len() {
            if let (Token::Word { lower: l1, .. }, Token::Word { lower: l2, .. }) =
                (&toks[idx], &toks[idx + 1])
            {
                if l1 == "as" {
                    if let Some(fw) = FORMAT_WORD(Some(l2)) {
                        as_at = Some(idx);
                        format = Some(fw);
                        break;
                    }
                }
            }
            idx += 1;
        }
        let Some(as_at) = as_at else {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Save expects as <format> to file after the value.".to_string(),
                "Write Save <value> as json to file <name>.".to_string(),
            );
            return Stmt::Note;
        };
        let format = format.unwrap_or("json");
        let value = self.value_position_expr(toks[ts.pos..as_at].to_vec(), Some(s), sc);
        ts.pos = as_at + 2; // as + <format>
        if !ts.consume_word("to") {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Save expects to file <name> after the format word.".to_string(),
                "Write Save <value> as json to file <name>.".to_string(),
            );
            return Stmt::Note;
        }
        let fr = match self.parse_file_ref(ts, s, None) {
            Some(fr) => fr,
            None => return Stmt::Note,
        };
        Stmt::SaveFormat {
            value,
            format: format.to_string(),
            file: fr,
        }
    }

    /// M4-G47: When file <ref> changes. with its indented block. A stray
    /// When (a sentence of Look at, a plain word) stays a Note.
    fn parse_when_file(
        &mut self,
        s: &'a Sentence,
        toks: &[Token],
        sc: &mut Scope,
        env: &mut OwnEnv,
    ) -> Stmt {
        let _ = sc;
        // ---- M4-10 (Appendix K G73/G74/G75): the network When shapes
        // (When someone gets PAGE. / When someone opens live PAGE.)
        if let Some(Token::Word { lower, .. }) = toks.get(1) {
            if lower == "someone" {
                return self.parse_when_network(s, toks, env).unwrap_or(Stmt::Note);
            }
        }
        // ---- M4-8 (Appendix K 7.10): When signal stop arrives. (G22/G23)
        let signal_shape = toks.len() >= 4
            && matches!(
                toks.get(1),
                Some(Token::Word { lower, .. }) if lower == "signal"
            );
        if signal_shape {
            let name = match toks.get(2) {
                Some(Token::Word { lower, .. }) if lower == "stop" => SignalName::Stop,
                Some(Token::Word { lower, .. }) if lower == "interrupt" => SignalName::Interrupt,
                Some(Token::Word { lower, .. }) if lower == "hangup" => SignalName::Hangup,
                _ => {
                    self.err(
                        "T0113",
                        "A signal sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "The signal is one of stop, interrupt or hangup.".to_string(),
                        "Write When signal stop arrives.".to_string(),
                    );
                    return Stmt::Note;
                }
            };
            let arrives_ok =
                matches!(
                    toks.get(3),
                    Some(Token::Word { lower, .. }) if lower == "arrives"
                ) && matches!(toks.get(4), Some(Token::Period) | Some(Token::Eof) | None);
            if !arrives_ok {
                self.err(
                    "T0113",
                    "A signal sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "Only `arrives` belongs after the signal; the steps go on the lines under it."
                        .to_string(),
                    "Write When signal stop arrives. with its body indented under it.".to_string(),
                );
                return Stmt::Note;
            }
            if s.children.is_empty() {
                self.err(
                    "T0113",
                    "A signal sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "When signal stop arrives. needs its steps on indented lines under it."
                        .to_string(),
                    "Indent the steps under When signal stop arrives.".to_string(),
                );
                return Stmt::Note;
            }
            // the signal block is a task (M4-S79): the task capture rules
            let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
            self.fn_outer_changeables = self
                .top_defs
                .iter()
                .filter(|(_, m)| *m)
                .map(|(n, _)| n.clone())
                .collect();
            self.in_task += 1;
            let mut tsc = self.top_seed_scope();
            let body = self.build_block(&s.children, &mut tsc, false, env);
            self.in_task -= 1;
            self.fn_outer_changeables = saved_oc;
            return Stmt::WhenSignal { signal: name, body };
        }
        let is_file_shape = toks.len() >= 4
            && matches!(
                toks.get(1),
                Some(Token::Word { lower, .. })
                    if lower == "file" || lower == "folder"
            )
            && toks
                .iter()
                .filter(|t| matches!(t, Token::Word { .. }))
                .last()
                .and_then(|t| match t {
                    Token::Word { lower, .. } => Some(lower.as_str()),
                    _ => None,
                })
                == Some("changes");
        if !is_file_shape {
            // T0119 (ch.21): a When block belongs under Look at, a screen
            // or a server; a stray When is an error, not a silent Note
            // (the Look at's own Whens are built by the look parse)
            self.err(
                "T0119",
                "When in the wrong place.".to_string(),
                s,
                0,
                s.text.len(),
                "A When block is not inside Look at, a screen or a server.".to_string(),
                "Put it under Look at.".to_string(),
            );
            return Stmt::Note;
        }
        let mut ts = TS::new(toks);
        ts.pos += 1; // when
        let Some(fr) = self.parse_file_ref(&mut ts, s, Some("changes")) else {
            return Stmt::Note;
        };
        // exactly `changes` remains on the line
        if !ts.consume_word("changes")
            || !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None)
        {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Only `changes` belongs after the file; the steps go on the lines under it."
                    .to_string(),
                "Write When file <name> changes. with its body indented under it.".to_string(),
            );
            return Stmt::Note;
        }
        if s.children.is_empty() {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "When file F changes. needs its steps on indented lines under it.".to_string(),
                "Indent the steps under When file <name> changes.".to_string(),
            );
            return Stmt::Note;
        }
        // the watcher body uses the task capture rules (like timers)
        let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
        self.fn_outer_changeables = self
            .top_defs
            .iter()
            .filter(|(_, m)| *m)
            .map(|(n, _)| n.clone())
            .collect();
        self.in_task += 1;
        let mut tsc = self.top_seed_scope();
        let body = self.build_block(&s.children, &mut tsc, false, env);
        self.in_task -= 1;
        self.fn_outer_changeables = saved_oc;
        Stmt::WhenFileChanges { file: fr, body }
    }

    // ============================================================ M4-10 (Appendix K 5.5/7.8) network

    /// M4-G78 (S59): the Page sentences are scanned before the body
    /// builds, so a Fetch address and a When someone sentence can name
    /// a page written later in the file. Tolerant here: a malformed
    /// Page sentence is reported again at its own build.
    fn prescan_pages(&mut self, roots: &[usize]) {
        for &idx in roots {
            let s = &self.all[idx];
            if first_word_lower(&s.text) != "page" {
                continue;
            }
            let toks = toks_of(&s.text);
            let mut ts = TS::new(&toks);
            ts.pos += 1; // page
            let mut name_words: Vec<String> = Vec::new();
            while let Some(t) = ts.peek() {
                match t {
                    Token::Word { lower, .. } if lower == "is" => break,
                    Token::Word { lower, .. } => {
                        name_words.push(lower.clone());
                        ts.pos += 1;
                    }
                    _ => break,
                }
            }
            if name_words.is_empty() || !ts.consume_word("is") {
                continue;
            }
            if let Some(segments) = self.parse_page_segments(&mut ts, s) {
                let name = name_words.join(" ");
                if !self.page_table.iter().any(|(n, _)| *n == name) {
                    self.page_table.push((name, segments));
                }
            }
        }
    }

    /// M4-G79/G80: the path segments after `is`: `nothing`, or a
    /// segment repeated (`and` segment). A segment is a word run
    /// (several words join with -, S67) or `anything called NAME`.
    fn parse_page_segments(&mut self, ts: &mut TS, s: &'a Sentence) -> Option<Vec<PageSeg>> {
        let mut segs: Vec<PageSeg> = Vec::new();
        if ts.peek_word() == Some("nothing") {
            ts.pos += 1;
            return Some(segs);
        }
        loop {
            if ts.peek_word() == Some("anything") {
                ts.pos += 1;
                if !ts.consume_word("called") {
                    self.err(
                        "T0113",
                        "A page sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "The segment that takes any value is written anything called NAME."
                            .to_string(),
                        "Write Page user page is users and anything called id.".to_string(),
                    );
                    return None;
                }
                let name = ts.peek_word().unwrap_or("").to_ascii_lowercase();
                ts.pos += 1;
                if name.is_empty() {
                    self.err(
                        "T0113",
                        "A page sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "anything called needs the parameter's name.".to_string(),
                        "Write Page user page is users and anything called id.".to_string(),
                    );
                    return None;
                }
                segs.push(PageSeg::Param(name));
            } else {
                let mut words: Vec<String> = Vec::new();
                while let Some(w) = ts.peek_word() {
                    if w == "and" {
                        break;
                    }
                    words.push(w.to_ascii_lowercase());
                    ts.pos += 1;
                }
                if words.is_empty() {
                    self.err(
                        "T0113",
                        "A page sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Every page path segment is a word or anything called NAME.".to_string(),
                        "Write Page users page is users.".to_string(),
                    );
                    return None;
                }
                segs.push(PageSeg::Lit(words.join("-")));
            }
            if !ts.consume_word("and") {
                break;
            }
        }
        Some(segs)
    }

    /// M4-G78: Page NAMES is SEGMENTS. at its own place: the segments
    /// are checked and the page is declared (the table row is already
    /// in place from the pre-scan).
    fn parse_page(&mut self, s: &'a Sentence, toks: &[Token]) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // page
        let mut name_words: Vec<String> = Vec::new();
        while let Some(t) = ts.peek() {
            match t {
                Token::Word { lower, .. } if lower == "is" => break,
                Token::Word { lower, .. } => {
                    name_words.push(lower.clone());
                    ts.pos += 1;
                }
                _ => break,
            }
        }
        if name_words.is_empty() {
            self.err(
                "T0113",
                "A page sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Page is written Page <name words> is <segments>.".to_string(),
                "Write Page users page is users.".to_string(),
            );
            return Stmt::Note;
        }
        if !ts.consume_word("is") {
            self.err(
                "T0113",
                "A page sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The page's path comes after is.".to_string(),
                "Write Page users page is users.".to_string(),
            );
            return Stmt::Note;
        }
        let Some(segments) = self.parse_page_segments(&mut ts, s) else {
            return Stmt::Note;
        };
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A page sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The page sentence ends after the path.".to_string(),
                "Write Page users page is users.".to_string(),
            );
            return Stmt::Note;
        }
        Stmt::PageDecl {
            name: name_words.join(" "),
            segments,
        }
    }

    /// The page NAME's pattern from the table (S59/S66); `home` is the
    /// built-in page for /.
    fn page_pattern(&self, name: &str) -> Option<Vec<PageSeg>> {
        if name == "home" {
            return Some(Vec::new());
        }
        self.page_table
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, p)| p.clone())
    }

    /// M4-G62..G66: one address: optional scheme (secure/plain), host
    /// words joined with dot, optional port, optional place (a page
    /// name from the Page table, T0173 when unknown, or path with
    /// literal segments).
    fn parse_net_address(&mut self, ts: &mut TS, s: &'a Sentence) -> Option<NetAddress> {
        // scheme: secure/plain, unless the word is the host's own first
        // (the next word is dot, as in secure dot example)
        let mut secure = true;
        let scheme_like =
            |w: &str, next: Option<&str>| (w == "secure" || w == "plain") && next != Some("dot");
        if let Some(w) = ts.peek_word() {
            if scheme_like(
                w,
                ts.toks.get(ts.pos + 1).and_then(|t| match t {
                    Token::Word { lower, .. } => Some(lower.as_str()),
                    _ => None,
                }),
            ) {
                secure = w == "secure";
                ts.pos += 1;
            }
        }
        // host words: NAME (dot NAME)*; an IP is numbers joined by dot
        // (S58); a host word that carries its own dot is T0171
        let mut host_parts: Vec<String> = Vec::new();
        loop {
            match ts.peek() {
                Some(Token::Word { lower, .. }) => {
                    if matches!(
                        lower.as_str(),
                        "dot" | "on" | "path" | "using" | "with" | "without"
                    ) {
                        break;
                    }
                    if lower.contains('.') {
                        self.err(
                            "T0170",
                            "Bad address.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "An address is written wrongly.".to_string(),
                            "Join host words with dot.".to_string(),
                        );
                        return None;
                    }
                    host_parts.push(lower.clone());
                    ts.pos += 1;
                }
                Some(Token::Whole { value }) => {
                    host_parts.push(value.to_string());
                    ts.pos += 1;
                }
                _ => break,
            }
            if !ts.consume_word("dot") {
                break;
            }
        }
        // T0170: a dot written as punctuation inside the address
        // (`Fetch example.com.` - the host words join with the word dot;
        // the sentence-ending period is the only Period with nothing
        // after it)
        if matches!(ts.peek(), Some(Token::Period))
            && matches!(ts.toks.get(ts.pos + 1), Some(Token::Word { .. }))
        {
            self.err(
                "T0170",
                "Bad address.".to_string(),
                s,
                0,
                s.text.len(),
                "An address is written wrongly.".to_string(),
                "Join host words with dot.".to_string(),
            );
            return None;
        }
        if host_parts.is_empty() {
            self.err(
                "T0170",
                "Bad address.".to_string(),
                s,
                0,
                s.text.len(),
                "An address is written wrongly.".to_string(),
                "Write Fetch example dot com.".to_string(),
            );
            return None;
        }
        // port (G65)
        let mut port: u16 = if secure { 443 } else { 80 };
        if ts.peek_word() == Some("on") {
            let next = ts.toks.get(ts.pos + 1).and_then(|t| match t {
                Token::Word { lower, .. } => Some(lower.as_str()),
                _ => None,
            });
            if next == Some("port") {
                ts.pos += 2;
                match ts.peek() {
                    Some(Token::Whole { value }) if *value > 0 && *value <= 65535 => {
                        port = *value as u16;
                        ts.pos += 1;
                    }
                    _ => {
                        self.err(
                            "T0171",
                            "An address is written wrongly.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The port is a whole number from 1 to 65535.".to_string(),
                            "Write Fetch example dot com on port 8080.".to_string(),
                        );
                        return None;
                    }
                }
            }
        }
        // place (G66): path with literal segments, or a page name
        let mut path = String::new();
        if ts.peek_word() == Some("path") {
            ts.pos += 1;
            let mut segs: Vec<String> = Vec::new();
            loop {
                let mut words: Vec<String> = Vec::new();
                loop {
                    match ts.peek() {
                        Some(Token::Word { lower, .. }) => {
                            let w = lower.as_str();
                            if w == "and" || w == "using" || w == "with" || w == "without" {
                                break;
                            }
                            words.push(w.to_ascii_lowercase());
                            ts.pos += 1;
                        }
                        // a number is a literal segment too (path user and 42)
                        Some(Token::Whole { value }) => {
                            words.push(value.to_string());
                            ts.pos += 1;
                        }
                        _ => break,
                    }
                }
                if words.is_empty() {
                    break;
                }
                segs.push(words.join("-"));
                if !ts.consume_word("and") {
                    break;
                }
            }
            if segs.is_empty() {
                self.err(
                    "T0171",
                    "An address is written wrongly.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "path is followed by literal segments joined by and.".to_string(),
                    "Write Fetch example dot com path users and 42.".to_string(),
                );
                return None;
            }
            path = format!("/{}", segs.join("/"));
        } else {
            let mut name_words: Vec<String> = Vec::new();
            while let Some(w) = ts.peek_word() {
                if w == "using" || w == "with" || w == "without" {
                    break;
                }
                name_words.push(w.to_ascii_lowercase());
                ts.pos += 1;
            }
            if !name_words.is_empty() {
                let name = name_words.join(" ");
                match self.page_pattern(&name) {
                    Some(pattern) => {
                        // S59: a fetch's place is literal; a page whose
                        // path takes a value (anything called NAME)
                        // cannot be fetched without the value (logged)
                        if pattern.iter().any(|p| matches!(p, PageSeg::Param(_))) {
                            self.err("T0171", "An address is written wrongly.".to_string(), s, 0, s.text.len(),
                                format!("The page {name} takes a value in its path, so it cannot be fetched."),
                                "Use path with the literal segments instead.".to_string());
                            return None;
                        }
                        let segs: Vec<String> = pattern
                            .into_iter()
                            .filter_map(|p| match p {
                                PageSeg::Lit(w) => Some(w),
                                PageSeg::Param(_) => None,
                            })
                            .collect();
                        path = if segs.is_empty() {
                            "/".to_string()
                        } else {
                            format!("/{}", segs.join("/"))
                        };
                    }
                    None => {
                        self.err("T0173", format!("The address names an unknown page {name}."), s, 0, s.text.len(),
                            "A page name is looked up in the Page sentences; no Page sentence declares it.".to_string(),
                            "Write Page users page is users. first, or use path users.".to_string());
                        return None;
                    }
                }
            }
        }
        Some(NetAddress {
            secure,
            host: host_parts.join("."),
            port,
            path,
        })
    }

    /// M4-G68: the clauses after an address: using METHOD, with data,
    /// with header, with query, without checking certificates.
    fn parse_fetch_clauses(
        &mut self,
        ts: &mut TS,
        s: &'a Sentence,
        sc: &mut Scope,
    ) -> (
        Option<NetMethod>,
        Option<Expr>,
        Vec<(String, Expr)>,
        Vec<(String, Expr)>,
        bool,
    ) {
        let mut method: Option<NetMethod> = None;
        let mut data: Option<Expr> = None;
        let mut headers: Vec<(String, Expr)> = Vec::new();
        let mut query: Vec<(String, Expr)> = Vec::new();
        let mut skip_tls = false;
        loop {
            match ts.peek_word() {
                Some("using") => {
                    ts.pos += 1;
                    let w = ts.peek_word().unwrap_or("");
                    match NetMethod::from_word(w) {
                        Some(m) => {
                            if method.is_some() {
                                self.err(
                                    "T0113",
                                    "A fetch sentence cannot be read.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    "One using clause sets the method.".to_string(),
                                    "Write Fetch example dot com using post.".to_string(),
                                );
                            }
                            method = Some(m);
                            ts.pos += 1;
                        }
                        None => {
                            self.err(
                                "T0113",
                                "A fetch sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "The method is the word get, post, put, delete or patch."
                                    .to_string(),
                                "Write Fetch example dot com using post.".to_string(),
                            );
                            return (method, data, headers, query, skip_tls);
                        }
                    }
                }
                Some("with") => {
                    ts.pos += 1;
                    let which = match ts.peek_word() {
                        Some(w) => w.to_string(),
                        None => String::new(),
                    };
                    ts.pos += 1;
                    match which.as_str() {
                        "data" => {
                            if data.is_some() {
                                self.err(
                                    "T0113",
                                    "A fetch sentence cannot be read.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    "One with data clause sets the body.".to_string(),
                                    "Write one with data clause.".to_string(),
                                );
                            }
                            let rest = ts.rest_without_period();
                            data = Some(self.value_position_expr(rest, Some(s), sc));
                            ts.pos = ts.toks.len();
                        }
                        "header" | "query" => {
                            // NAME x: the value starts at the first
                            // number or known name; the words before it
                            // are the NAME (joined by -, S60; logged cut
                            // for the ambiguity's tie-break). When every
                            // word is a name candidate, the last word is
                            // the value.
                            let mut name_words: Vec<String> = Vec::new();
                            let mut i = ts.pos;
                            while i < ts.toks.len() {
                                match &ts.toks[i] {
                                    Token::Word { lower, .. }
                                        if lower != "and"
                                            && sc.find(lower).is_none()
                                            && !self.names.iter().any(|n| n == lower) =>
                                    {
                                        name_words.push(lower.clone());
                                        i += 1;
                                    }
                                    _ => break,
                                }
                            }
                            if name_words.is_empty() {
                                self.err(
                                    "T0113",
                                    "A fetch sentence cannot be read.".to_string(),
                                    s,
                                    0,
                                    s.text.len(),
                                    "The clause is written with header NAME value.".to_string(),
                                    "Write with header content type hello.".to_string(),
                                );
                                return (method, data, headers, query, skip_tls);
                            }
                            // the run may end at the sentence's period too
                            let at_end = i >= ts.toks.len()
                                || matches!(ts.toks[i], Token::Period | Token::Eof);
                            if at_end && i > ts.pos {
                                i -= 1;
                                name_words.pop();
                            }
                            let value_toks = ts.toks[i..ts.toks.len()].to_vec();
                            let value = self.value_position_expr(value_toks, Some(s), sc);
                            let name = name_words.join("-");
                            if which == "header" {
                                headers.push((name, value));
                            } else {
                                query.push((name, value));
                            }
                            ts.pos = ts.toks.len();
                        }
                        _ => {
                            self.err(
                                "T0113",
                                "A fetch sentence cannot be read.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "A with clause carries data, a header or a query.".to_string(),
                                "Write with data hello.".to_string(),
                            );
                            return (method, data, headers, query, skip_tls);
                        }
                    }
                }
                Some("without") => {
                    // S62: without checking certificates (Be careful only)
                    let ws: Vec<&str> = ts.toks[ts.pos..]
                        .iter()
                        .filter_map(|t| match t {
                            Token::Word { lower, .. } => Some(lower.as_str()),
                            _ => None,
                        })
                        .collect();
                    if ws.get(1) == Some(&"checking") && ws.get(2) == Some(&"certificates") {
                        if self.in_careful == 0 {
                            self.err(
                                "T0521",
                                "Certificate checks skipped outside Be careful.".to_string(),
                                s,
                                0,
                                s.text.len(),
                                "without checking certificates is only legal inside Be careful."
                                    .to_string(),
                                "Put it in Be careful.".to_string(),
                            );
                        }
                        skip_tls = true;
                        ts.pos += 3;
                    } else {
                        self.err(
                            "T0113",
                            "A fetch sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The only without clause is without checking certificates.".to_string(),
                            "Write without checking certificates.".to_string(),
                        );
                        return (method, data, headers, query, skip_tls);
                    }
                }
                _ => break,
            }
        }
        (method, data, headers, query, skip_tls)
    }

    /// M4-G67: Fetch ADDRESS [clauses]. - one HTTP request; the
    /// response record lands in it (S60).
    fn parse_fetch(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // fetch
        let Some(address) = self.parse_net_address(&mut ts, s) else {
            return Stmt::Note;
        };
        let (method, data, headers, query, skip_tls) = self.parse_fetch_clauses(&mut ts, s, sc);
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A fetch sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The fetch sentence ends after its clauses.".to_string(),
                "Write Fetch example dot com.".to_string(),
            );
            return Stmt::Note;
        }
        Stmt::Fetch {
            method: method.unwrap_or(NetMethod::Get),
            address,
            data,
            headers,
            query,
            skip_tls,
        }
    }

    /// M4-G70: Post DATA to ADDRESS. (S60: a Fetch using post with the
    /// data).
    fn parse_post(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // post
        let data_toks = ts.rest_until_word("to");
        if data_toks.is_empty() {
            self.err(
                "T0113",
                "A post sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Post is written Post DATA to ADDRESS.".to_string(),
                "Write Post hello to example dot com.".to_string(),
            );
            return Stmt::Note;
        }
        let data = self.value_position_expr(data_toks, Some(s), sc);
        if !ts.consume_word("to") {
            self.err(
                "T0113",
                "A post sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The address comes after to.".to_string(),
                "Write Post hello to example dot com.".to_string(),
            );
            return Stmt::Note;
        }
        let Some(address) = self.parse_net_address(&mut ts, s) else {
            return Stmt::Note;
        };
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A post sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The post sentence ends after the address.".to_string(),
                "Write Post hello to example dot com.".to_string(),
            );
            return Stmt::Note;
        }
        Stmt::PostTo { data, address }
    }

    /// M4-G76: Respond with TEXT | json X | status N [and TEXT] |
    /// template NAME | literally TEXT. Only inside a handler body.
    fn parse_respond(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        if self.in_handler == 0 {
            self.err(
                "T0113",
                "Respond runs outside a handler.".to_string(),
                s,
                0,
                s.text.len(),
                "Respond belongs in a When someone block.".to_string(),
                "Write it in the body of When someone gets users page.".to_string(),
            );
            return Stmt::Note;
        }
        let mut ts = TS::new(toks);
        ts.pos += 1; // respond
        if !ts.consume_word("with") {
            self.err(
                "T0113",
                "A respond sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Respond is written Respond with ...".to_string(),
                "Write Respond with hello.".to_string(),
            );
            return Stmt::Note;
        }
        let kind = match ts.peek_word() {
            Some("json") => {
                ts.pos += 1;
                let rest = ts.rest_without_period();
                if rest.is_empty() {
                    self.err(
                        "T0113",
                        "A respond sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Respond with json needs the value.".to_string(),
                        "Write Respond with json answer.".to_string(),
                    );
                    return Stmt::Note;
                }
                RespondKind::Json(self.value_position_expr(rest, Some(s), sc))
            }
            Some("status") => {
                ts.pos += 1;
                let n = match ts.peek() {
                    Some(Token::Whole { value }) => {
                        let v = *value;
                        ts.pos += 1;
                        v
                    }
                    _ => {
                        self.err(
                            "T0113",
                            "A respond sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The status is a whole number.".to_string(),
                            "Write Respond with status 404.".to_string(),
                        );
                        return Stmt::Note;
                    }
                };
                if ts.consume_word("and") {
                    let content = ts.rest_without_period();
                    if content.is_empty() {
                        self.err(
                            "T0113",
                            "A respond sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The status body comes after and.".to_string(),
                            "Write Respond with status 404 and not found.".to_string(),
                        );
                        return Stmt::Note;
                    }
                    RespondKind::Status(n, Some(self.parse_expr(content, Some(s), sc, true)))
                } else {
                    RespondKind::Status(n, None)
                }
            }
            Some("template") => {
                ts.pos += 1;
                let mut name_words: Vec<String> = Vec::new();
                while let Some(w) = ts.peek_word() {
                    name_words.push(w.to_ascii_lowercase());
                    ts.pos += 1;
                }
                if name_words.is_empty() {
                    self.err(
                        "T0113",
                        "A respond sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Respond with template needs the template's name.".to_string(),
                        "Write Respond with template hello.".to_string(),
                    );
                    return Stmt::Note;
                }
                let name = name_words.join(" ");
                // T0172 at build time: the file NAME.template must sit
                // in the source folder (S69)
                let path = std::path::Path::new(&self.source_dir).join(format!("{name}.template"));
                if !path.is_file() {
                    self.err("T0172", format!("The template {name} is missing."), s, 0, s.text.len(),
                        "Respond with template fills the file NAME.template in the source folder; there is none.".to_string(),
                        format!("Write the file {name}.template next to the program."));
                }
                RespondKind::Template(name)
            }
            Some("literally") => {
                ts.pos += 1;
                let content = ts.rest_without_period();
                if content.is_empty() {
                    self.err(
                        "T0113",
                        "A respond sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Respond with literally needs the text.".to_string(),
                        "Write Respond with literally json.".to_string(),
                    );
                    return Stmt::Note;
                }
                // the raw text: no name substitution (S69)
                RespondKind::Literally(flat_words(&content))
            }
            _ => {
                // the raw text (S69: even if it starts with json, the
                // word `literally` makes the text form explicit). The
                // text is read as a Say reads it (text-taking word,
                // Appendix K 4), so several words join with spaces.
                let content = ts.rest_without_period();
                if content.is_empty() {
                    self.err(
                        "T0113",
                        "A respond sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Respond with needs the answer.".to_string(),
                        "Write Respond with hello.".to_string(),
                    );
                    return Stmt::Note;
                }
                RespondKind::Text(self.parse_expr(content, Some(s), sc, true))
            }
        };
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A respond sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The respond sentence ends after the answer.".to_string(),
                "Write Respond with hello.".to_string(),
            );
            return Stmt::Note;
        }
        let _ = sc;
        Stmt::Respond { kind }
    }

    /// M4-G71/G72: Serve [securely] on port NUMBER. [using certificate
    /// file F and key file F.] with its indented block (S64).
    fn parse_serve(
        &mut self,
        s: &'a Sentence,
        toks: &[Token],
        sc: &mut Scope,
        env: &mut OwnEnv,
    ) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // serve
        let secure = if ts.peek_word() == Some("securely") {
            ts.pos += 1;
            true
        } else {
            false
        };
        if !ts.consume_word("on") || ts.peek_word() != Some("port") {
            self.err(
                "T0113",
                "A serve sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Serve is written Serve on port NUMBER.".to_string(),
                "Write Serve on port 8080.".to_string(),
            );
            return Stmt::Note;
        }
        ts.pos += 1; // port
        let port = match ts.peek() {
            Some(Token::Whole { value }) if *value > 0 && *value <= 65535 => {
                let p = *value;
                ts.pos += 1;
                p
            }
            _ => {
                self.err(
                    "T0113",
                    "A serve sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The port is a whole number from 1 to 65535.".to_string(),
                    "Write Serve on port 8080.".to_string(),
                );
                return Stmt::Note;
            }
        };
        let (mut cert, mut key) = (None, None);
        if ts.peek_word() == Some("using") {
            ts.pos += 1;
            if !ts.consume_word("certificate") {
                self.err(
                    "T0113",
                    "A serve sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The TLS files come as using certificate file F and key file F.".to_string(),
                    "Write Serve securely on port 8443 using certificate file C and key file K."
                        .to_string(),
                );
                return Stmt::Note;
            }
            cert = self.parse_file_ref(&mut ts, s, Some("and"));
            if cert.is_none() {
                return Stmt::Note;
            }
            if !ts.consume_word("and") || !ts.consume_word("key") {
                self.err(
                    "T0113",
                    "A serve sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The key file comes after the certificate, joined by and.".to_string(),
                    "Write Serve securely on port 8443 using certificate file C and key file K."
                        .to_string(),
                );
                return Stmt::Note;
            }
            key = self.parse_file_ref(&mut ts, s, None);
            if key.is_none() {
                return Stmt::Note;
            }
        }
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A serve sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "The serve sentence ends after the port and the TLS files.".to_string(),
                "Write Serve on port 8080.".to_string(),
            );
            return Stmt::Note;
        }
        if s.children.is_empty() {
            self.err(
                "T0113",
                "A serve sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Serve. needs its steps on indented lines under it.".to_string(),
                "Indent the When someone blocks under Serve.".to_string(),
            );
            return Stmt::Note;
        }
        self.in_serve += 1;
        let body = self.build_block(&s.children, sc, false, env);
        self.in_serve -= 1;
        Stmt::Serve {
            port: port as u16,
            secure,
            cert,
            key,
            body,
        }
    }

    /// M4-S68 (T0166/T0167): the per-path Respond check.
    /// `falls_through` is true when some path reaches the end of the list
    /// without a Respond; `two` is true when some path reaches two
    /// Responds. Respond ends the body (Flow::Stop), so the first Respond
    /// in a list ends that path; nested blocks fork.
    fn respond_paths(stmts: &[Stmt]) -> (bool, bool) {
        let mut falls = true;
        let mut two = false;
        let mut respond_seen = false;
        for st in stmts {
            match st {
                Stmt::Respond { .. } => {
                    // a second Respond in the same list is two on the
                    // path (the later one is dead, but it is written on
                    // the path - T0167)
                    if respond_seen {
                        two = true;
                    } else {
                        respond_seen = true;
                        falls = false;
                    }
                }
                _ if !respond_seen => match st {
                    Stmt::If { branches, other } => {
                        // the path takes one branch; a missing Otherwise is
                        // the empty else path
                        let mut branch_falls = branches.is_empty();
                        for (_, body) in branches {
                            let (f, t) = Self::respond_paths(body);
                            two |= t;
                            branch_falls |= f;
                        }
                        let else_falls = match other {
                            Some(o) => {
                                let (f, t) = Self::respond_paths(o);
                                two |= t;
                                f
                            }
                            None => true,
                        };
                        falls = branch_falls || else_falls;
                    }
                    Stmt::Try {
                        sentence,
                        success,
                        failure,
                    } => {
                        let (f0, t0) = Self::respond_paths(std::slice::from_ref(sentence.as_ref()));
                        let (f1, t1) = Self::respond_paths(success);
                        two |= t0 | t1;
                        let mut ff = f0 && f1;
                        for (_, body) in failure {
                            let (f, t) = Self::respond_paths(body);
                            two |= t;
                            ff |= f;
                        }
                        falls = ff;
                    }
                    Stmt::Careful { body }
                    | Stmt::DoTogether { body }
                    | Stmt::AfterTimer { body, .. }
                    | Stmt::EveryTimer { body, .. } => {
                        // the body runs inline; a path through the body is
                        // the path through the sentence
                        let (f, t) = Self::respond_paths(body);
                        two |= t;
                        falls = f;
                    }
                    Stmt::RepeatTimes { body, .. }
                    | Stmt::RepeatForever { body }
                    | Stmt::RepeatWhile { body, .. }
                    | Stmt::ForRange { body, .. }
                    | Stmt::ForIn { body, .. }
                    | Stmt::StreamLoop { body, .. }
                    | Stmt::ForEachLine { body, .. }
                    | Stmt::ForEachInput { body, .. }
                    | Stmt::Spread { body, .. } => {
                        // the loop body's fall path loops again; a path can
                        // also skip the loop (0 rounds): the path continues
                        // after it
                        let (_, t) = Self::respond_paths(body);
                        two |= t;
                    }
                    _ => {} // no nested statement list: the path continues
                },
                // dead after a Respond: the body already ended
                _ => {}
            }
        }
        (falls, two)
    }

    /// M4-G73/G74/G75: When someone gets|posts|puts|deletes|patches
    /// PAGE. (a handler) or When someone opens live PAGE. (a WebSocket
    /// live block). Both belong inside a Serve block (S64); the page is
    /// looked up in the Page table (T0173).
    fn parse_when_network(
        &mut self,
        s: &'a Sentence,
        toks: &[Token],
        env: &mut OwnEnv,
    ) -> Option<Stmt> {
        let second = match toks.get(1) {
            Some(Token::Word { lower, .. }) => lower.as_str(),
            _ => return None,
        };
        if second != "someone" {
            return None;
        }
        let third = match toks.get(2) {
            Some(Token::Word { lower, .. }) => lower.as_str(),
            _ => return None,
        };
        let is_live = third == "opens";
        let method = if is_live {
            if toks.get(3).and_then(|t| match t {
                Token::Word { lower, .. } => Some(lower.as_str()),
                _ => None,
            }) != Some("live")
            {
                self.err(
                    "T0113",
                    "A live sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "When someone opens is followed by live and the page.".to_string(),
                    "Write When someone opens live chat page.".to_string(),
                );
                return Some(Stmt::Note);
            }
            None
        } else {
            match NetMethod::from_word(third.trim_end_matches('s')) {
                Some(m) => Some(m),
                None => return None, // a plain When of a Look at
            }
        };
        if self.in_serve == 0 {
            // T0165 (Appendix K): a When someone is not in a Serve block
            self.err(
                "T0165",
                "When someone outside Serve.".to_string(),
                s,
                0,
                s.text.len(),
                "When someone is not in a Serve block.".to_string(),
                "Put it in Serve.".to_string(),
            );
            return Some(Stmt::Note);
        }
        // the page name words run to the sentence end
        let start = if is_live { 4 } else { 3 };
        let mut name_words: Vec<String> = Vec::new();
        for t in &toks[start..] {
            match t {
                Token::Word { lower, .. } => name_words.push(lower.clone()),
                _ => {}
            }
        }
        if name_words.is_empty() {
            self.err(
                "T0113",
                "A handler sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "When someone needs the page it answers.".to_string(),
                "Write When someone gets users page.".to_string(),
            );
            return Some(Stmt::Note);
        }
        let name = name_words.join(" ");
        let Some(pattern) = self.page_pattern(&name) else {
            self.err(
                "T0173",
                format!("The handler names an unknown page {name}."),
                s,
                0,
                s.text.len(),
                "A page name is looked up in the Page sentences; no Page sentence declares it."
                    .to_string(),
                "Write Page users page is users. first.".to_string(),
            );
            return Some(Stmt::Note);
        };
        if s.children.is_empty() {
            self.err(
                "T0113",
                "A handler sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "When someone needs its steps on indented lines under it.".to_string(),
                "Indent the steps under When someone gets users page.".to_string(),
            );
            return Some(Stmt::Note);
        }
        // M4-S65: the handler is a task; it sees the same names as a
        // task block (the capture rules apply, T0451), with session
        // provided (S68; logged cut for the guarded-capture checks in
        // the eager model)
        let saved_oc = std::mem::take(&mut self.fn_outer_changeables);
        self.fn_outer_changeables = self
            .top_defs
            .iter()
            .filter(|(_, m)| *m)
            .map(|(n, _)| n.clone())
            .collect();
        self.in_task += 1;
        if is_live {
            self.in_live += 1;
        } else {
            self.in_handler += 1;
        }
        let mut tsc = self.top_seed_scope();
        tsc.define(
            "session",
            Def {
                kind: Kind::Map(Box::new(Kind::Text), Box::new(Kind::Text)),
                mutable: true,
                shared: false,
            },
        );
        // M4-S73/D13: inside a live block the provided connection is a
        // real value of the connection kind (a copy kind storable in
        // lists and maps); the runtime binds it in the session's scope.
        if is_live {
            tsc.define(
                "connection",
                Def {
                    kind: Kind::Connection,
                    mutable: false,
                    shared: false,
                },
            );
        }
        let body = self.build_block(&s.children, &mut tsc, false, env);
        if is_live {
            self.in_live -= 1;
        } else {
            self.in_handler -= 1;
        }
        self.in_task -= 1;
        self.fn_outer_changeables = saved_oc;
        if is_live {
            Some(Stmt::WhenLive {
                page: name,
                pattern,
                body,
            })
        } else {
            // T0166/T0167 (S68): per path - every path must reach one
            // Respond and no path may reach two
            let (falls, two) = Self::respond_paths(&body);
            if falls {
                self.err(
                    "T0166",
                    "A handler path has no Respond.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "Every path of a When someone body must reach one Respond with.".to_string(),
                    "Add Respond with ... to the body.".to_string(),
                );
            } else if two {
                self.err(
                    "T0167",
                    "Handler responds twice.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "A path has two Respond sentences.".to_string(),
                    "Keep one.".to_string(),
                );
            }
            Some(Stmt::WhenSomeone {
                method: method.unwrap_or(NetMethod::Get),
                page: name,
                pattern,
                body,
            })
        }
    }

    /// M4-G77 (S68): one row of the reads of request, parsed before the
    /// record-part speculation (request is not a declared record).
    fn try_request_read(&mut self, ts: &mut TS, lower: &str) -> Option<Expr> {
        let simple = match lower {
            "method" => Some((RequestRow::Method, Kind::Text)),
            "page" => Some((RequestRow::Page, Kind::Text)),
            "text" => Some((RequestRow::Text, Kind::Text)),
            "data" => Some((RequestRow::Data, Kind::List(Box::new(Kind::Whole)))),
            _ => None,
        };
        if let Some((row, kind)) = simple {
            let next2: Vec<Option<&str>> = (1..=2)
                .map(|k| {
                    ts.toks.get(ts.pos + k).and_then(|t| match t {
                        Token::Word { lower, .. } => Some(lower.as_str()),
                        _ => None,
                    })
                })
                .collect();
            if next2[0] == Some("of") && next2[1] == Some("request") {
                ts.pos += 3;
                return Some(Expr {
                    kind,
                    e: E::RequestRead { row },
                    dis: format!("{lower} of request"),
                    can_fail: false,
                    num_word: false,
                });
            }
            return None;
        }
        // header/query/parameter NAME of request
        let take = match lower {
            "header" => "header",
            "query" => "query",
            "parameter" => "parameter",
            _ => return None,
        };
        let mut name_words: Vec<String> = Vec::new();
        let mut i = ts.pos + 1;
        while let Some(t) = ts.toks.get(i) {
            match t {
                Token::Word { lower: w, .. } if w != "of" => {
                    name_words.push(w.clone());
                    i += 1;
                }
                _ => break,
            }
        }
        let next = ts.toks.get(i).and_then(|t| match t {
            Token::Word { lower, .. } => Some(lower.as_str()),
            _ => None,
        });
        let next2 = ts.toks.get(i + 1).and_then(|t| match t {
            Token::Word { lower, .. } => Some(lower.as_str()),
            _ => None,
        });
        if name_words.is_empty() || next != Some("of") || next2 != Some("request") {
            return None;
        }
        let name = name_words.join("-");
        let row = match take {
            "header" => RequestRow::Header(name),
            "query" => RequestRow::Query(name),
            _ => RequestRow::Parameter(name),
        };
        ts.pos = i + 2;
        Some(Expr {
            kind: Kind::Maybe(Box::new(Kind::Text)),
            e: E::RequestRead { row },
            dis: format!("{take} of request"),
            can_fail: false,
            num_word: false,
        })
    }

    // ------------------------------------------------------------ say

    fn parse_put(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // put
        let value_toks = ts.rest_until_word("in");
        let value = self.value_position_expr(value_toks, Some(s), sc);
        ts.pos += 1; // in
        let map = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => String::new(),
        };
        ts.pos += 1;
        let key = if ts.consume_word("under") {
            let key_toks = ts.rest_without_period();
            Some(self.value_position_expr(key_toks, Some(s), sc))
        } else {
            None
        };
        // T0308 (M2): the key must have the key kind the map was declared
        // with (`map of K to V`). A name whose kind is unknown is not checked.
        if let (Some(k), Some(def)) = (key.as_ref(), sc.find(&map)) {
            if let Kind::Map(want_key, _) = &def.kind {
                if !kind_fits(want_key, &k.kind) {
                    let (a, b) = {
                        let (a, b) = name_span(&s.text, &k.dis);
                        if a == b { (0, s.text.len()) } else { (a, b) }
                    };
                    self.err(
                        "T0308",
                        "Map key kind differs.".to_string(),
                        s,
                        a,
                        b,
                        "A key does not match the kind of the map.".to_string(),
                        "Use the key kind.".to_string(),
                    );
                }
            }
        }
        Stmt::Put { map, key, value }
    }

    /// Remove <value> from <coll>, or Remove first from <coll>. (M2)
    fn parse_remove(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // remove
        if ts.peek_word() == Some("first") {
            ts.pos += 1;
            ts.consume_word("from");
            let coll = match ts.peek_word() {
                Some(w) => w.to_ascii_lowercase(),
                None => String::new(),
            };
            ts.pos += 1;
            return Stmt::RemoveFirst { coll };
        }
        let value_toks = ts.rest_until_word("from");
        let value = self.value_position_expr(value_toks, Some(s), sc);
        ts.pos += 1; // from
        let coll = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => String::new(),
        };
        ts.pos += 1;
        Stmt::Remove { coll, value }
    }

    /// Parse an expression in a value position: an unknown word there is text
    /// (Ch.4 rule 2), as opposed to a math-operand position (rule 3).
    fn value_position_expr(
        &mut self,
        toks: Vec<Token>,
        s: Option<&'a Sentence>,
        sc: &Scope,
    ) -> Expr {
        self.text_depth += 1;
        let e = self.parse_expr(toks, s, sc, false);
        self.text_depth -= 1;
        e
    }

    // ------------------------------------------------------------ statements

    /// `<name> is <value>.` / `Changeable <name> is <value>.`
    /// / `Constant <name> is <value>.`
    fn parse_decl(&mut self, s: &'a Sentence, toks: Vec<Token>, sc: &mut Scope) -> Stmt {
        let lower = first_word_lower(&s.text);
        let mut ts = TS::new(&toks);
        let mutable = lower == "changeable";
        let is_const = lower == "constant";
        if mutable || is_const {
            ts.pos += 1;
        }
        let mut name_words: Vec<String> = Vec::new();
        while ts.pos < ts.toks.len() {
            if ts.peek_word() == Some("is") {
                break;
            }
            if let Some(w) = ts.peek_word() {
                name_words.push(w.to_string());
            }
            ts.pos += 1;
        }
        ts.consume_word("is");
        // the articles the/a/an are removed from code (ch.4): `The words
        // is ...` defines `words`
        if name_words.first().map_or(false, |w| {
            matches!(w.to_ascii_lowercase().as_str(), "the" | "a" | "an")
        }) {
            name_words.remove(0);
        }
        let name = name_words.join(" ").to_ascii_lowercase();
        if name.is_empty() {
            return Stmt::Note; // reported by the syntax layer
        }
        // T0201 (S3): a name is defined once in the block where it lives;
        // a second definition of a name already visible, in the same
        // block or an outer one, is an error (the scope holds the
        // enclosing blocks' names, so this is exactly the visible set)
        if sc.find(&name).is_some() {
            let spelling = name_words.join(" ");
            let (lo, hi) = span_of(&s.text, &spelling);
            self.err(
                "T0201",
                "Defined twice.".to_string(),
                s,
                lo,
                hi,
                "A name is defined again in scope.".to_string(),
                "Use Changeable and Set.".to_string(),
            );
        }
        // Collection type definition? `map of K to V`, `set of T`, `array of N T`, ...
        if let Some(expr) = self.parse_coll_type(&mut ts, Some(s)) {
            sc.define(
                &name,
                Def {
                    kind: expr.kind.clone(),
                    mutable,
                    shared: false,
                },
            );
            return Stmt::Define(Decl {
                name,
                mutable,
                is_const,
                expr,
                fallback: None,
                shared: false,
            });
        }
        let after = ts.rest_without_period();
        // the value of a definition is a value position (Ch.4, rule 2): a run
        // of plain words there is one text, as in Line is cat sat down. The
        // flat walk still recognizes calls (Result is double 21.) and names.
        // The name being defined is not in scope until its sentence ends.
        self.defining = Some(name.clone());
        self.text_depth += 1;
        let mut expr = self.parse_expr(after, Some(s), sc, true);
        self.text_depth -= 1;
        self.defining = None;
        if expr.num_word && expr.kind != Kind::Text {
            self.err(
                "T0006",
                "Number spelled as letters.".to_string(),
                s,
                0,
                s.text.len(),
                "A number is written as a word where a number is expected.".to_string(),
                "Write the number with digits. To make the word a text value, write as text."
                    .to_string(),
            );
        }
        if expr.kind == Kind::Missing {
            self.err("T0303",
                format!("Lykaon cannot tell what kind of value {name} holds. Add as and the kind, for example: as maybe number."),
                s, 0, s.text.len(),
                "Lykaon cannot work out the kind of a value.".to_string(),
                "Add as and the kind.".to_string());
            expr.kind = Kind::Unknown;
        }
        if sc.find(&name).is_some() {
            self.err(
                "T0207",
                format!("{name} is defined twice."),
                s,
                0,
                s.text.len(),
                "A name is defined again where it is already visible.".to_string(),
                "Give the value a new name, or reuse the first one.".to_string(),
            );
        }
        let shared = self.shared_names.contains(&name);
        sc.define(
            &name,
            Def {
                kind: expr.kind.clone(),
                mutable,
                shared,
            },
        );
        Stmt::Define(Decl {
            name,
            mutable,
            is_const,
            expr,
            fallback: None,
            shared,
        })
    }

    /// Parse a collection *type* written after `is`:
    ///   `map of K to V`  |  `set of T`  |  `queue of T`  |  `array of N T`  |  `empty list of T`
    ///
    /// Returns None when the tokens are not a collection type, in which case the
    /// ordinary value-expression path handles them (e.g. `list of 5 and 2 and 8`).
    fn parse_coll_type(&mut self, ts: &mut TS, _s: Option<&'a Sentence>) -> Option<Expr> {
        let mut trial = ts.clone();
        let word = trial.peek_word()?;
        let mut size = None;
        let kind = match word {
            "map" => {
                trial.pos += 1;
                if !trial.consume_word("of") {
                    return None;
                }
                let k = self.coll_type_word(&mut trial)?;
                if !trial.consume_word("to") {
                    return None;
                }
                let v = self.coll_type_word(&mut trial)?;
                Kind::Map(Box::new(k), Box::new(v))
            }
            "set" => {
                trial.pos += 1;
                if !trial.consume_word("of") {
                    return None;
                }
                let k = self.coll_type_word(&mut trial)?;
                Kind::Set(Box::new(k))
            }
            "queue" => {
                trial.pos += 1;
                if !trial.consume_word("of") {
                    return None;
                }
                let k = self.coll_type_word(&mut trial)?;
                Kind::Queue(Box::new(k))
            }
            "array" => {
                trial.pos += 1;
                if !trial.consume_word("of") {
                    return None;
                }
                if let Some(Token::Whole { value }) = trial.peek() {
                    size = Some(*value as usize);
                    trial.pos += 1;
                } else {
                    return None;
                }
                let k = self.coll_type_word(&mut trial)?;
                Kind::Array(Box::new(k))
            }
            "empty" => {
                trial.pos += 1;
                match trial.peek_word() {
                    Some("list") => {
                        trial.pos += 1;
                        if !trial.consume_word("of") {
                            return None;
                        }
                        Kind::List(Box::new(self.coll_type_word(&mut trial)?))
                    }
                    Some("queue") => {
                        trial.pos += 1;
                        if !trial.consume_word("of") {
                            return None;
                        }
                        Kind::Queue(Box::new(self.coll_type_word(&mut trial)?))
                    }
                    Some("set") => {
                        trial.pos += 1;
                        if !trial.consume_word("of") {
                            return None;
                        }
                        Kind::Set(Box::new(self.coll_type_word(&mut trial)?))
                    }
                    _ => return None,
                }
            }
            "maybe" => {
                // `Phone is maybe number.` - the maybe kind (ch.18)
                trial.pos += 1;
                Kind::Maybe(Box::new(
                    self.coll_type_word(&mut trial).unwrap_or(Kind::Unknown),
                ))
            }
            _ => return None,
        };
        *ts = trial;
        Some(Expr {
            kind: kind.clone(),
            e: E::CollEmpty { kind, size },
            dis: "collection".to_string(),
            can_fail: false,
            num_word: false,
        })
    }

    /// One base kind word in a type position (M2-D4: `number` means whole number).
    fn coll_type_word(&mut self, ts: &mut TS) -> Option<Kind> {
        match ts.peek_word() {
            Some("number") | Some("whole") | Some("numbers") => {
                ts.pos += 1;
                if ts.peek_word() == Some("number") {
                    ts.pos += 1;
                } // "whole number" -> whole
                Some(Kind::Whole)
            }
            Some("decimal") => {
                ts.pos += 1;
                Some(Kind::Decimal)
            }
            Some("text") => {
                ts.pos += 1;
                Some(Kind::Text)
            }
            Some("yes") => {
                ts.pos += 1;
                if ts.consume_word("or") && ts.consume_word("no") {
                    Some(Kind::Boolean)
                } else {
                    None
                }
            }
            Some("letter") => {
                ts.pos += 1;
                Some(Kind::Letter)
            }
            // ---- M4-7 (Appendix K 7.7): the time and secret kinds ----
            Some("date") => {
                ts.pos += 1;
                Some(Kind::Date)
            }
            Some("moment") => {
                ts.pos += 1;
                Some(Kind::Moment)
            }
            Some("duration") => {
                ts.pos += 1;
                Some(Kind::Duration)
            }
            Some("secret") => {
                ts.pos += 1;
                // M4-S56: the kind secret T where T is text or bytes.
                // Bytes are not values in this cut, so `secret` (and the
                // spelled-out `secret text`) is the secret of text
                // (logged); `secret bytes` leaves the word bytes
                // unconsumed, which the sentence reader refuses.
                if ts.peek_word() == Some("text") {
                    ts.pos += 1;
                }
                Some(Kind::Secret(Box::new(Kind::Text)))
            }
            Some("list") => {
                ts.pos += 1;
                if ts.consume_word("of") {
                    let inner = self.coll_type_word(ts).unwrap_or(Kind::Unknown);
                    Some(Kind::List(Box::new(inner)))
                } else {
                    None
                }
            }
            Some("map") => {
                ts.pos += 1;
                if ts.consume_word("of") {
                    let k = self.coll_type_word(ts).unwrap_or(Kind::Unknown);
                    if ts.consume_word("to") {
                        let v = self.coll_type_word(ts).unwrap_or(Kind::Unknown);
                        Some(Kind::Map(Box::new(k), Box::new(v)))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Some("set") => {
                ts.pos += 1;
                if ts.consume_word("of") {
                    Some(Kind::Set(Box::new(
                        self.coll_type_word(ts).unwrap_or(Kind::Unknown),
                    )))
                } else {
                    None
                }
            }
            Some("queue") => {
                ts.pos += 1;
                if ts.consume_word("of") {
                    Some(Kind::Queue(Box::new(
                        self.coll_type_word(ts).unwrap_or(Kind::Unknown),
                    )))
                } else {
                    None
                }
            }
            Some("maybe") => {
                ts.pos += 1;
                Some(Kind::Maybe(Box::new(
                    self.coll_type_word(ts).unwrap_or(Kind::Unknown),
                )))
            }
            Some("pair") => {
                ts.pos += 1;
                if ts.consume_word("of") {
                    let a = self.coll_type_word(ts).unwrap_or(Kind::Unknown);
                    if ts.consume_word("and") {
                        let b = self.coll_type_word(ts).unwrap_or(Kind::Unknown);
                        Some(Kind::Pair(Box::new(a), Box::new(b)))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Some(w) => {
                // a declared record type used as a part kind (ch.20)
                let name = w.to_string();
                if let Some(parts) = self.record_types.get(&name).cloned() {
                    ts.pos += 1;
                    Some(Kind::Record(name, parts))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// M4-6 (S42): the T of `as T` in the format sentences. A declared
    /// enum name is a type word here (S45: an enum decodes), which the
    /// collection type words do not take yet.
    fn format_type_word(&mut self, ts: &mut TS) -> Option<Kind> {
        if let Some(w) = ts.peek_word() {
            let name = w.to_string();
            if let Some(variants) = self.enum_types.get(&name).cloned() {
                ts.pos += 1;
                return Some(Kind::Enum(variants));
            }
        }
        self.coll_type_word(ts)
    }

    /// M4-6: the compile-time shape check of `as T`. Only the S42
    /// targets decode: a record, an enum, a list, a map of text to
    /// something, a maybe or a base kind (whole, decimal, text,
    /// yes-or-no, letter) - and csv takes a list of one record kind
    /// only (S47). Anything else is a shape error (logged; the doc
    /// gives the rule before the bad-format wording at run time).
    fn check_format_target(&mut self, format: &str, target: &Kind, s: &'a Sentence) {
        let ok = match format {
            "csv" => {
                matches!(target, Kind::List(inner) if matches!(**inner, Kind::Record(..)))
            }
            _ => Self::format_target_ok(target),
        };
        if !ok {
            self.err(
                "T0113",
                "A file sentence cannot be read.".to_string(),
                s, 0, s.text.len(),
                format!("{format} does not decode into this kind."),
                if format == "csv" {
                    "Write Read {format} file <name> as list of <record name>.".to_string()
                } else {
                    "The kind after as takes a record, enum, list, map of text, maybe or a base kind.".to_string()
                },
            );
        }
    }

    /// The S42 shape of a decodable target kind (records and enums
    /// hold already-checked parts; Unknown stays open). M4-6.
    fn format_target_ok(k: &Kind) -> bool {
        match k {
            Kind::Record(..) | Kind::Enum(..) | Kind::Unknown => true,
            Kind::List(inner) | Kind::Maybe(inner) => Self::format_target_ok(inner),
            Kind::Map(k, v) if matches!(**k, Kind::Text | Kind::Unknown) => {
                Self::format_target_ok(v)
            }
            Kind::Whole | Kind::Decimal | Kind::Text | Kind::Boolean | Kind::Letter => true,
            _ => false,
        }
    }

    /// Set <name> to <value>.
    fn parse_set(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1;
        // Set age of maya to 32. / Set street of home of maya to Oak. (ch.20)
        if let Some(path) = self.try_part_path(&mut ts) {
            let base = path[path.len() - 1].clone();
            if ts.peek_word() == Some("to") {
                ts.pos += 1;
            }
            let expr = self.parse_expr(ts.rest_without_period(), Some(s), sc, false);
            let (lo, hi) = span_of(&s.text, &base);
            match sc.find(&base) {
                Some(d) => {
                    if !d.mutable {
                        self.err("T0406", format!("{base} is fixed and cannot be changed."), s, lo, hi,
                            format!("{base} was defined without Changeable, and the outermost name must be Changeable to set a part."),
                            format!("Define it as Changeable {base} is <first value>."));
                    }
                }
                None => {
                    if let Some(m) = crate::unshared_module_of(&base) {
                        self.err(
                            "T0208",
                            format!(
                                "{base} is not shared by {m}. Add Share {base}. to {m}.lykaon."
                            ),
                            s,
                            lo,
                            hi,
                            format!("{base} belongs to module {m}, which does not share it."),
                            format!("Add Share {base}. to {m}.lykaon, or use a shared name."),
                        );
                    } else {
                        self.err(
                            "T0205",
                            format!("{base} is not defined."),
                            s,
                            lo,
                            hi,
                            format!("{base} is used where it is not defined."),
                            "Define it first, or check the spelling.".to_string(),
                        );
                    }
                }
            }
            return Stmt::SetPart { path, expr };
        }
        let name = self.match_name(&mut ts).unwrap_or_default();
        if ts.peek_word() == Some("to") {
            ts.pos += 1;
        }
        let expr = self.parse_expr(ts.rest_without_period(), Some(s), sc, false);
        let (lo, hi) = span_of(&s.text, &name);
        match sc.find(&name) {
            Some(d) => {
                if matches!(d.kind, Kind::Share) {
                    // T0412: a shared value cannot be changed (ch.28); this
                    // outranks the plain fixed-name rule
                    self.err(
                        "T0412",
                        format!("{name} is shared and cannot be changed."),
                        s,
                        lo,
                        hi,
                        "Set is used on a shared value.".to_string(),
                        "Change a copy, or use guarded.".to_string(),
                    );
                } else if !d.mutable && !matches!(d.kind, Kind::Guarded(_)) {
                    // M4-D3 (Appendix K): a guarded name changes through Set.
                    if matches!(d.kind, Kind::Atomic | Kind::Counter) {
                        self.err("T0406", format!("{name} is fixed and cannot be changed."), s, lo, hi,
                            format!("{name} is an atomic number or counter; it changes with Add, not Set."),
                            format!("Add <number> to {name}. or Add <number> to {name} atomically."));
                    } else {
                        self.err(
                            "T0406",
                            format!("{name} is fixed and cannot be changed."),
                            s,
                            lo,
                            hi,
                            format!("{name} was defined without Changeable."),
                            format!("Define it as Changeable {name} is <first value>."),
                        );
                    }
                }
                // T0304 (S1): a name is set to a value of a different kind
                // (the Guarded wrapper is transparent: the inner kind is
                // the value's kind)
                let unwrap = |k: &Kind| match k {
                    Kind::Guarded(inner) => inner.as_ref().clone(),
                    k => k.clone(),
                };
                let set_kind = unwrap(&d.kind);
                let val_kind = unwrap(&expr.kind);
                let kind_mismatch = !matches!(set_kind, Kind::Unknown | Kind::Missing)
                    && !matches!(val_kind, Kind::Unknown | Kind::Missing)
                    && set_kind != val_kind
                    && !matches!(set_kind, Kind::Atomic | Kind::Counter);
                if kind_mismatch {
                    self.err(
                        "T0304",
                        format!("{name} is set to a value of a different kind."),
                        s,
                        lo,
                        hi,
                        "A name is set to a value of a different kind.".to_string(),
                        "Keep one kind.".to_string(),
                    );
                }
            }
            None => {
                if let Some(m) = crate::unshared_module_of(&name) {
                    self.err(
                        "T0208",
                        format!("{name} is not shared by {m}. Add Share {name}. to {m}.lykaon."),
                        s,
                        lo,
                        hi,
                        format!("{name} belongs to module {m}, which does not share it."),
                        format!("Add Share {name}. to {m}.lykaon, or use a shared name."),
                    );
                } else {
                    self.err(
                        "T0205",
                        format!("{name} is not defined."),
                        s,
                        lo,
                        hi,
                        format!("{name} is used where it is not defined."),
                        "Define it first, or check the spelling.".to_string(),
                    );
                }
            }
        }
        Stmt::Set { name, expr }
    }

    /// The part path of a Set target: age of maya -> [age, maya]; the words
    /// run part of part of ... base (the outermost name last).
    fn try_part_path(&mut self, ts: &mut TS) -> Option<Vec<String>> {
        let save = ts.pos;
        let mut path: Vec<String> = Vec::new();
        loop {
            let w = match ts.peek_word() {
                Some(w) => w.to_ascii_lowercase(),
                None => break,
            };
            if ts.peek_next() != Some("of") {
                // the last word is the base record name
                path.push(w);
                ts.pos += 1;
                break;
            }
            path.push(w);
            ts.pos += 2; // word + of
        }
        // at least one part and one base
        if path.len() >= 2 {
            Some(path)
        } else {
            ts.pos = save;
            None
        }
    }

    /// A/An <name> has part as K and ... / A/An <name> is shape or shape
    /// with part as K. (ch.20 / ch.21)
    fn parse_type_decl(&mut self, s: &'a Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // a / an
        let tname = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => return Stmt::Note,
        };
        ts.pos += 1;
        if ts.peek_word() == Some("has") {
            ts.pos += 1;
            let mut parts: Vec<(String, Kind)> = Vec::new();
            loop {
                let p = match ts.peek_word() {
                    Some(w) => w.to_ascii_lowercase(),
                    None => break,
                };
                ts.pos += 1;
                let mut kind = Kind::Unknown;
                if ts.consume_word("as") {
                    kind = self.coll_type_word(&mut ts).unwrap_or(Kind::Unknown);
                }
                parts.push((p, kind));
                if ts.peek_word() == Some("and") {
                    ts.pos += 1;
                    continue;
                }
                break;
            }
            self.record_types.insert(tname.clone(), parts.clone());
            // the Always block of a record (ch.64, M3-S38): `Always cond.`
            // children say what is true of every value of the kind
            for &c in &s.children {
                let cs = &self.all[c];
                if first_word_lower(&cs.text) != "always" {
                    continue;
                }
                let (atok, _) = Lexer::new(&cs.text).tokenize();
                let mut ats = TS::new(&atok);
                ats.pos += 1; // Always
                // Full value access in Always (ch.64): every part keeps its
                // declared kind, and the whole value is reachable under the
                // kind name, `value` and `original`, so `age of value` and
                // `x of value of the kind` read inside the condition. A part
                // named value or original keeps its own binding.
                let self_kind = Kind::Record(tname.clone(), parts.clone());
                let mut asc = Scope::default();
                for (p, k) in &parts {
                    asc.define(
                        p,
                        Def {
                            kind: k.clone(),
                            mutable: false,
                            shared: false,
                        },
                    );
                }
                asc.define(
                    &tname,
                    Def {
                        kind: self_kind.clone(),
                        mutable: false,
                        shared: false,
                    },
                );
                for extra in ["value", "original"] {
                    if !parts.iter().any(|(p, _)| p == extra) {
                        asc.define(
                            extra,
                            Def {
                                kind: self_kind.clone(),
                                mutable: false,
                                shared: false,
                            },
                        );
                    }
                }
                let cond = self.parse_condition(ats.rest_without_period(), Some(cs), &asc);
                // this declaration is parsed twice (the pre-function hoist
                // and the real statement pass); the kinds map is an insert
                // and dedupes for free, but Always entries would register
                // twice ï¿½ once is already the second visit's twin
                if !self
                    .always
                    .iter()
                    .any(|(t, c)| t == &tname && c.line == cs.line)
                {
                    self.always.push((
                        tname.clone(),
                        Contract {
                            cond,
                            checked: false,
                            is_ensures: false,
                            line: cs.line,
                            text: cs.text.trim().trim_end_matches('.').to_string(),
                        },
                    ));
                }
            }
            return Stmt::Note;
        }
        if ts.peek_word() == Some("can") {
            // A dog can speak. (function impl, ch.23) or a special meaning
            // block: A point can add. (ch.26, M3-D4)
            ts.pos += 1;
            let mut words: Vec<String> = Vec::new();
            while let Some(w) = ts.peek_word() {
                words.push(w.to_ascii_lowercase());
                ts.pos += 1;
            }
            let verb = words.join(" ");
            let (meaning, verb_name) = match verb.as_str() {
                "add" => (Some(Meaning::Add), verb.clone()),
                "compare" => (Some(Meaning::Compare), verb.clone()),
                "copy" => (Some(Meaning::Copy), verb.clone()),
                "clean up" => (Some(Meaning::CleanUp), verb.clone()),
                "be saved" => (Some(Meaning::Saved), "be saved".to_string()),
                _ => (None, verb.clone()),
            };
            let mut func_impls: Vec<FuncDef> = Vec::new();
            let mut body: Vec<Stmt> = Vec::new();
            let mut child_sc = sc.child();
            let mut env = OwnEnv::new();
            if meaning.is_none() {
                // function impl: each child is a To definition whose first
                // input is the kind itself (M3-S16)
                for &c in &s.children {
                    let cs = &self.all[c];
                    if first_word_lower(&cs.text) != "to" {
                        continue;
                    }
                    if let Some(mut f) = self.parse_function(cs, true) {
                        f.is_local = false;
                        func_impls.push(f);
                    }
                }
            } else {
                // meaning impl: statements with the provided names (section 7.4)
                let provided: Vec<String> = match &meaning {
                    Some(Meaning::Add) | Some(Meaning::Compare) => {
                        vec!["left".into(), "right".into()]
                    }
                    Some(Meaning::Copy) | Some(Meaning::Saved) => {
                        vec!["original".into(), "value".into()]
                    }
                    _ => vec![tname.clone()],
                };
                // left and right carry the kind itself with its declared
                // parts, so `x of left` resolves (ch.26: inside the block
                // left and right are the two values)
                let self_kind = match self.record_types.get(tname.as_str()) {
                    Some(parts) => Kind::Record(tname.clone(), parts.clone()),
                    None => Kind::Record(tname.clone(), Vec::new()),
                };
                for p in &provided {
                    child_sc.define(
                        p,
                        Def {
                            kind: self_kind.clone(),
                            mutable: true,
                            shared: false,
                        },
                    );
                    env.vars.insert(
                        p.clone(),
                        VarState {
                            kind: self_kind.clone(),
                            mutable: true,
                            alive: true,
                            mode: ParamMode::Lent,
                        },
                    );
                    env.params.push(p.clone());
                }
                body = self.build_block(&s.children, &mut child_sc, false, &mut env);
            }
            self.impls.push(ImplBlock {
                kind_name: tname.clone(),
                verb: verb_name,
                meaning,
                funcs: func_impls,
                body,
                line: s.line,
            });
            return Stmt::Note;
        }
        if ts.peek_word() == Some("is") {
            ts.pos += 1;
            let mut variants: Vec<(String, Vec<(String, Kind)>)> = Vec::new();
            loop {
                let shape = match ts.peek_word() {
                    Some(w) => w.to_ascii_lowercase(),
                    None => break,
                };
                ts.pos += 1;
                let mut parts: Vec<(String, Kind)> = Vec::new();
                if ts.peek_word() == Some("with") {
                    ts.pos += 1;
                    loop {
                        let p = match ts.peek_word() {
                            Some(w) => w.to_ascii_lowercase(),
                            None => break,
                        };
                        ts.pos += 1;
                        let mut kind = Kind::Unknown;
                        if ts.consume_word("as") {
                            kind = self.coll_type_word(&mut ts).unwrap_or(Kind::Unknown);
                        }
                        parts.push((p, kind));
                        if ts.peek_word() == Some("and") {
                            ts.pos += 1;
                            continue;
                        }
                        break;
                    }
                }
                self.shape_names
                    .insert(shape.clone(), (tname.clone(), parts.clone()));
                variants.push((shape, parts));
                if ts.peek_word() == Some("or") {
                    ts.pos += 1;
                    continue;
                }
                break;
            }
            self.enum_types.insert(tname.clone(), variants.clone());
            // the names of the shapes are names (ch.21): every variant value
            // belongs to this enum
            let ekind = Kind::Enum(variants.clone());
            for (shape, _) in &variants {
                sc.define(
                    shape,
                    Def {
                        kind: ekind.clone(),
                        mutable: false,
                        shared: false,
                    },
                );
            }
            return Stmt::DefineEnum {
                name: tname,
                variants,
            };
        }
        Stmt::Note
    }

    /// Look at <value>. The When children take an enum apart (ch.21).
    fn parse_look(
        &mut self,
        s: &'a Sentence,
        toks: &[Token],
        sc: &mut Scope,
        env: &mut OwnEnv,
    ) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // look
        ts.consume_word("at");
        let value = self.parse_expr(ts.rest_without_period(), Some(s), &*sc, false);
        let variants: Vec<(String, Vec<(String, Kind)>)> = match &value.kind {
            Kind::Enum(vs) => vs.clone(),
            _ => Vec::new(),
        };
        let mut whens: Vec<When> = Vec::new();
        let mut seen: Vec<String> = Vec::new();
        // T0118 (ch.21): a Look at has no When block
        let has_when = s.children.iter().any(|&c| {
            self.all[c]
                .text
                .split_whitespace()
                .next()
                .map_or(false, |w| w.eq_ignore_ascii_case("when"))
        });
        if !has_when {
            self.err(
                "T0118",
                "Look at without When.".to_string(),
                s,
                0,
                s.text.len(),
                "Look at has no When block.".to_string(),
                "Add a When block for each shape.".to_string(),
            );
            return Stmt::Note;
        }
        for &c in &s.children {
            let cs = &self.all[c];
            let (ctoks, _) = Lexer::new(&cs.text).tokenize();
            let mut cts = TS::new(&ctoks);
            cts.pos += 1; // when
            let shape = match cts.peek_word() {
                Some(w) => w.to_ascii_lowercase(),
                None => continue,
            };
            cts.pos += 1;
            let parts: Vec<(String, Kind)> = variants
                .iter()
                .find(|(v, _)| v == &shape)
                .map(|(_, p)| p.clone())
                .unwrap_or_default();
            let variants_known = !variants.is_empty();
            let mut names: Vec<String> = Vec::new();
            loop {
                let w = match cts.peek_word() {
                    Some(x) => x.to_ascii_lowercase(),
                    None => break,
                };
                cts.pos += 1;
                names.push(w);
            }
            if variants_known {
                if !variants.iter().any(|(v, _)| v == &shape) {
                    // a shape the enum does not have
                    self.err(
                        "T0315",
                        format!("{shape} is not a shape of this enum."),
                        cs,
                        0,
                        cs.text.len(),
                        format!("When {shape} names a shape the enum was not declared with."),
                        "Use one of the declared shapes.".to_string(),
                    );
                } else if seen.iter().any(|v| v == &shape) {
                    self.err(
                        "T0321",
                        format!("Look at covers {shape} more than once."),
                        cs,
                        0,
                        cs.text.len(),
                        format!("Two When blocks handle {shape}."),
                        "One When block per shape.".to_string(),
                    );
                } else if names.len() != parts.len() {
                    self.err(
                        "T0322",
                        format!("When {shape} has the wrong number of names."),
                        cs,
                        0,
                        cs.text.len(),
                        format!(
                            "{shape} carries {} parts, so When {} takes {} names.",
                            parts.len(),
                            shape,
                            parts.len()
                        ),
                        format!("Write When {shape} with one name per part."),
                    );
                }
            }
            let mut body_sc = sc.child();
            for (n, (p, k)) in names.iter().zip(parts.iter()) {
                let _ = p;
                body_sc.define(
                    n,
                    Def {
                        kind: k.clone(),
                        mutable: false,
                        shared: false,
                    },
                );
            }
            let body = self.build_block(&cs.children, &mut body_sc, false, env);
            seen.push(shape.clone());
            whens.push(When { shape, names, body });
        }
        // coverage: every variant gets a When (ch.21, T0320)
        for (v, _) in &variants {
            if !seen.iter().any(|x| x == v) {
                self.err(
                    "T0320",
                    format!(
                        "Look at {} does not cover {v}. Add a When {v} block.",
                        value.dis
                    ),
                    s,
                    0,
                    s.text.len(),
                    format!("{v} has no When block."),
                    format!("Add a When {v} block."),
                );
            }
        }
        Stmt::LookAt { value, whens }
    }

    /// Fail with TEXT. Only allowed inside a function declared can fail (T0332).
    fn parse_fail(&mut self, s: Option<&'a Sentence>, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // fail
        ts.consume_word("with");
        let message = self.parse_expr(ts.rest_without_period(), s, sc, true);
        if let Some(ss) = s {
            if !self.in_can_fail_fn {
                self.err(
                    "T0332",
                    "Fail with is used in a function not declared can fail.".to_string(),
                    ss,
                    0,
                    ss.text.len(),
                    "Fail with is allowed only in a function that says can fail.".to_string(),
                    "Declare the function can fail.".to_string(),
                );
            }
        }
        Stmt::Fail { message }
    }

    /// Pass failure up. Only allowed inside a can fail function (T0117).
    fn parse_pass(&mut self, s: Option<&'a Sentence>, _toks: &[Token], _sc: &mut Scope) -> Stmt {
        if !self.in_can_fail_fn {
            if let Some(ss) = s {
                self.err(
                    "T0117",
                    "Pass failure up. is not inside a function that can fail.".to_string(),
                    ss,
                    0,
                    ss.text.len(),
                    "Pass failure up. is allowed only inside a function that can fail.".to_string(),
                    "Declare the function can fail.".to_string(),
                );
            }
        }
        Stmt::PassFailureUp
    }

    /// Close x. drops x early (ch.31). Close can fail and is handled like any
    /// can fail sentence.
    fn parse_close(&mut self, s: Option<&'a Sentence>, toks: &[Token], _sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // close
        let name = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => String::new(),
        };
        ts.pos += 1;
        let _ = s;
        Stmt::Close { name }
    }

    /// Share <name>. marks a definition visible to other modules (ch.36).
    fn parse_share(&mut self, s: Option<&'a Sentence>, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // share
        let mut words: Vec<String> = Vec::new();
        while ts.pos < ts.toks.len() {
            if let Some(w) = ts.peek_word() {
                words.push(w.to_string());
            }
            ts.pos += 1;
        }
        let name = words.join(" ").to_ascii_lowercase();
        if name.is_empty() {
            return Stmt::Note;
        }
        self.shared_names.push(name.clone());
        // If the definition already exists, mark it shared.
        if let Some(digest) = sc.defs.iter_mut().find(|(n, _)| *n == name) {
            digest.1.shared = true;
        }
        let _ = s;
        Stmt::Share { name }
    }

    /// Use <name>. / Use <name> from <folder>. brings one module's shared
    /// definitions in (ch.36). The file load happens at compile time in `build`.
    fn parse_use(&mut self, s: Option<&'a Sentence>, toks: &[Token]) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // use
        let mut head: Vec<String> = Vec::new();
        let mut tail: Vec<String> = Vec::new();
        let mut in_from = false;
        while ts.pos < ts.toks.len() {
            if let Some(w) = ts.peek_word() {
                if w == "from" {
                    in_from = true;
                } else if in_from {
                    tail.push(w.to_string());
                } else {
                    head.push(w.to_string());
                }
            }
            ts.pos += 1;
        }
        let file = if tail.is_empty() {
            head.join(" ").to_ascii_lowercase()
        } else {
            format!(
                "{}/{}",
                tail.join(" ").to_ascii_lowercase(),
                head.join(" ").to_ascii_lowercase()
            )
        };
        let _ = s;
        Stmt::Use { file }
    }

    /// M4-G14/G15 share the Sleep duration grammar (M4-G5/G6): a NUMBER and
    /// a plural unit, starting at the first token of `toks`. Reports T0113
    /// on `s` when the shape is wrong.
    fn parse_duration(&mut self, s: Option<&'a Sentence>, toks: &[Token]) -> Option<(u64, String)> {
        let mut ts = TS::new(toks);
        let amount: u64 = match ts.peek().cloned() {
            Some(Token::Whole { value }) if value >= 0 => {
                ts.pos += 1;
                value as u64
            }
            _ => {
                if let Some(ss) = s {
                    self.err("T0113", "A timer sentence cannot be read.".to_string(), ss, 0, ss.text.len(),
                        "A timer needs a number of milliseconds, seconds, minutes, hours, days or weeks.".to_string(),
                        "Write After 5 seconds.".to_string());
                }
                return None;
            }
        };
        let unit = ts
            .peek_word()
            .map(|w| w.to_ascii_lowercase())
            .unwrap_or_default();
        match unit.as_str() {
            "milliseconds" | "seconds" | "minutes" | "hours" | "days" | "weeks" => {
                ts.pos += 1;
                Some((amount, unit))
            }
            _ => {
                if let Some(ss) = s {
                    self.err("T0113", "A timer sentence cannot be read.".to_string(), ss, 0, ss.text.len(),
                        "The timer needs a time unit.".to_string(),
                        "Write milliseconds, seconds, minutes, hours, days or weeks after the number.".to_string());
                }
                None
            }
        }
    }

    /// Check that <condition>. asserts inside a Test block (ch.38). Outside a
    /// test it is an error (T0156).
    fn parse_check(&mut self, s: Option<&'a Sentence>, toks: &[Token], sc: &mut Scope) -> Stmt {
        if self.in_test == 0 {
            if let Some(ss) = s {
                self.err(
                    "T0156",
                    "Check is used outside a Test.".to_string(),
                    ss,
                    0,
                    ss.text.len(),
                    "A check asserts something while a test runs.".to_string(),
                    "Move Check inside a Test block.".to_string(),
                );
            }
        }
        let mut ts = TS::new(toks);
        ts.pos += 1; // check
        if ts.peek_word() == Some("for") {
            // Check for any <kind> <name>. â€” property test (ch.38)
            let words: Vec<String> = ts
                .rest_without_period()
                .iter()
                .map(|t| match t {
                    Token::Word { text, .. } => text.clone(),
                    _ => String::new(),
                })
                .collect();
            // words: for any <kind words...> <name>
            if words.len() >= 4 && words[1].eq_ignore_ascii_case("any") {
                let kind = words[2..words.len() - 1].join(" ").to_ascii_lowercase();
                let name = words[words.len() - 1].to_ascii_lowercase();
                return Stmt::Check {
                    text: s.map(|x| x.text.clone()).unwrap_or_default(),
                    cond: None,
                    must_fail: false,
                    prop: Some((kind, name)),
                    body: vec![],
                };
            }
        }
        if ts.peek_word() != Some("that") {
            let _ = s;
            return Stmt::Check {
                text: s.map(|x| x.text.clone()).unwrap_or_default(),
                cond: None,
                must_fail: false,
                prop: None,
                body: vec![],
            };
        }
        ts.pos += 1;
        let cond = self.parse_condition(ts.rest_without_period(), s, &*sc);
        let _ = sc;
        Stmt::Check {
            text: s.map(|x| x.text.clone()).unwrap_or_default(),
            cond: Some(cond),
            must_fail: false,
            prop: None,
            body: vec![],
        }
    }

    /// Pretend <f> gives <V>. replaces a function "for now" (ch.38). Outside a
    /// test block it is an error (T0155).
    fn parse_pretend(&mut self, s: Option<&'a Sentence>, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1; // pretend
        let mut name_words: Vec<String> = Vec::new();
        while ts.pos < ts.toks.len() {
            match ts.peek_word() {
                Some("gives") => break,
                Some(w) => name_words.push(w.to_string()),
                _ => {}
            }
            ts.pos += 1;
        }
        let name = name_words.join(" ").to_ascii_lowercase();
        if self.in_test == 0 {
            if let Some(ss) = s {
                self.err(
                    "T0155",
                    "Pretend is used outside a Test.".to_string(),
                    ss,
                    0,
                    ss.text.len(),
                    "Pretend replaces a function only while a test runs.".to_string(),
                    "Move Pretend inside a Test block.".to_string(),
                );
            }
        }
        ts.consume_word("gives");
        self.text_depth += 1;
        let value = self.parse_expr(ts.rest_without_period(), s, &*sc, false);
        self.text_depth -= 1;
        Stmt::Pretend { name, value }
    }

    /// Ask <name> [as number|decimal|text]. The reply is text unless converted.
    fn parse_ask(&mut self, s: &Sentence, toks: &[Token], sc: &mut Scope) -> Stmt {
        let mut ts = TS::new(toks);
        ts.pos += 1;
        let name = ts.peek_word().unwrap_or("").to_ascii_lowercase();
        let lower = s.text.to_ascii_lowercase();
        let kind = if lower.contains(" as decimal") {
            AskKind::Decimal
        } else if lower.contains(" as number") {
            AskKind::Number
        } else {
            AskKind::Text
        };
        sc.define(
            &name,
            Def {
                kind: match kind {
                    AskKind::Text => Kind::Text,
                    AskKind::Number => Kind::Unknown, // a reply may be whole or decimal
                    AskKind::Decimal => Kind::Decimal,
                },
                mutable: true,
                shared: false,
            },
        );
        Stmt::Ask {
            name,
            kind,
            fallback: None,
        }
    }

    fn parse_repeat(&mut self, s: &'a Sentence, sc: &mut Scope, env: &mut OwnEnv) -> Option<Stmt> {
        let (toks, _) = Lexer::new(&s.text).tokenize();
        let mut ts = TS::new(&toks);
        ts.pos += 1;
        match ts.peek().cloned() {
            Some(Token::Whole { value }) => {
                ts.pos += 1;
                ts.consume_word("times");
                let body = if ts.peek_word().is_some()
                    && !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof))
                {
                    vec![self.parse_inline_body(ts.rest_without_period(), Some(s), sc)]
                } else {
                    self.build_block(&s.children, &mut sc.child(), false, env)
                };
                Some(Stmt::RepeatTimes {
                    count: lit_whole(value),
                    body,
                })
            }
            Some(Token::Word { lower, .. }) if lower == "while" => {
                ts.pos += 1;
                let cond = self.parse_condition(ts.rest_without_period(), Some(s), &*sc);
                let body = self.build_block(&s.children, &mut sc.child(), false, env);
                Some(Stmt::RepeatWhile { cond, body })
            }
            Some(Token::Word { lower, .. }) if lower == "forever" => {
                let body = self.build_block(&s.children, &mut sc.child(), false, env);
                Some(Stmt::RepeatForever { body })
            }
            _ => None,
        }
    }

    // ------------------------------------------------ M4-8 (7.11) tools

    /// M4-S81/G25/G26: collect the Takes and Option sentences of the
    /// program. They stand before every other sentence except Note and
    /// About (T0174 otherwise); a nested one never reaches here (only the
    /// top-level roots are walked) and is refused by the body dispatch.
    fn parse_tool_decls(&mut self, roots: &[usize]) -> (Vec<ToolArg>, Vec<ToolOpt>) {
        let mut takes: Vec<ToolArg> = Vec::new();
        let mut options: Vec<ToolOpt> = Vec::new();
        let mut seen_other = false;
        for &idx in roots {
            let s = &self.all[idx];
            let first = first_word_lower(&s.text);
            match first.as_str() {
                "takes" | "option" => {
                    self.tool_sentence_idx.push(idx);
                    if seen_other {
                        self.err("T0174", "A Takes or Option sentence stands after the program's sentences.".to_string(), s, 0, s.text.len(),
                            "Takes and Option stand before every other sentence of the program, except Note and About.".to_string(),
                            "Move the sentence above the other sentences.".to_string());
                        continue;
                    }
                    let (toks, _) = Lexer::new(&s.text).tokenize();
                    let mut ts = TS::new(&toks);
                    ts.pos += 1; // takes / option
                    if first == "takes" {
                        if let Some(t) = self.parse_takes_decl(&mut ts, s) {
                            takes.push(t);
                        }
                    } else if let Some(o) = self.parse_option_decl(&mut ts, s) {
                        options.push(o);
                    }
                }
                "note" | "about" => {}
                _ => seen_other = true,
            }
        }
        (takes, options)
    }

    /// Takes <name words> as [maybe] <kind>. (M4-G25)
    fn parse_takes_decl(&mut self, ts: &mut TS, s: &'a Sentence) -> Option<ToolArg> {
        let mut name_words: Vec<String> = Vec::new();
        loop {
            match ts.peek().cloned() {
                Some(Token::Word { lower, .. }) if lower != "as" => {
                    name_words.push(lower);
                    ts.pos += 1;
                }
                Some(Token::Word { .. }) => {
                    ts.pos += 1; // as
                    break;
                }
                _ => break,
            }
        }
        if name_words.is_empty() {
            self.err(
                "T0113",
                "A Takes sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Takes does not name a value.".to_string(),
                "Write Takes file name as text.".to_string(),
            );
            return None;
        }
        let Some((kind, maybe)) = self.parse_tool_kind(ts, s) else {
            return None;
        };
        // exactly the period remains
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "A Takes sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Only the kind belongs after as; the line ends there.".to_string(),
                "Write Takes file name as text.".to_string(),
            );
            return None;
        }
        Some(ToolArg {
            name: name_words.join(" "),
            kind,
            maybe,
        })
    }

    /// Option <name words> is [maybe] <kind> [defaulting to <literal>]. (M4-G26)
    fn parse_option_decl(&mut self, ts: &mut TS, s: &'a Sentence) -> Option<ToolOpt> {
        let mut name_words: Vec<String> = Vec::new();
        loop {
            match ts.peek().cloned() {
                Some(Token::Word { lower, .. }) if lower != "is" => {
                    name_words.push(lower);
                    ts.pos += 1;
                }
                Some(Token::Word { .. }) => {
                    ts.pos += 1; // is
                    break;
                }
                _ => break,
            }
        }
        if name_words.is_empty() {
            self.err(
                "T0113",
                "An Option sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Option does not name a value.".to_string(),
                "Write Option log level is text defaulting to debug.".to_string(),
            );
            return None;
        }
        let Some((kind, maybe)) = self.parse_tool_kind(ts, s) else {
            return None;
        };
        let mut default: Option<Value> = None;
        if ts.consume_word("defaulting") {
            if !ts.consume_word("to") {
                self.err(
                    "T0113",
                    "An Option sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "defaulting needs to and a value of the option's kind.".to_string(),
                    "Write Option log level is text defaulting to debug.".to_string(),
                );
                return None;
            }
            // the default is a literal value: a word for text, a number
            // for the number kinds (a non-literal default is refused -
            // logged)
            let v = match ts.peek().cloned() {
                Some(Token::Word { lower, .. }) => {
                    ts.pos += 1;
                    Some(Value::Text(lower))
                }
                Some(Token::Whole { value }) => {
                    ts.pos += 1;
                    Some(Value::Whole(value))
                }
                Some(Token::Decimal { value }) => {
                    ts.pos += 1;
                    Some(Value::Dec(value))
                }
                Some(Token::Negative { value }) => {
                    ts.pos += 1;
                    Some(Value::Whole(-value))
                }
                Some(Token::Missing) | Some(Token::Nothing) => {
                    ts.pos += 1;
                    Some(Value::Missing)
                }
                _ => None,
            };
            let Some(v) = v else {
                self.err(
                    "T0113",
                    "An Option sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The default of an option is one literal value of the option's kind."
                        .to_string(),
                    "Write Option log level is text defaulting to debug.".to_string(),
                );
                return None;
            };
            // the default's kind is the option's kind (a whole default for
            // a text option is a bad sentence)
            let kind_ok = match (&kind, &v) {
                (ToolKind::Text, Value::Text(_)) => true,
                (ToolKind::Whole, Value::Whole(_)) => true,
                (ToolKind::Decimal, Value::Dec(_) | Value::Whole(_)) => true,
                (ToolKind::Number, Value::Whole(_) | Value::Dec(_)) => true,
                _ => false,
            };
            if !kind_ok {
                self.err(
                    "T0113",
                    "An Option sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The default's kind is not the option's kind.".to_string(),
                    "Write Option count is whole number defaulting to 3.".to_string(),
                );
                return None;
            }
            default = Some(v);
        }
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
            self.err(
                "T0113",
                "An Option sentence cannot be read.".to_string(),
                s,
                0,
                s.text.len(),
                "Only defaulting to <value> belongs after the kind; the line ends there."
                    .to_string(),
                "Write Option log level is text defaulting to debug.".to_string(),
            );
            return None;
        }
        Some(ToolOpt {
            name: name_words.join(" "),
            kind,
            maybe,
            default,
        })
    }

    /// One tool kind spelling: [maybe] whole number | number | decimal |
    /// text. Other kinds (dates, secrets, collections) cannot come from a
    /// command line and are refused (logged: only the command-line kinds
    /// are Takes/Option kinds in this cut).
    fn parse_tool_kind(&mut self, ts: &mut TS, s: &'a Sentence) -> Option<(ToolKind, bool)> {
        let maybe = ts.peek_word() == Some("maybe");
        if maybe {
            ts.pos += 1;
        }
        let kind = match ts.peek_word() {
            Some("whole") => {
                ts.pos += 1;
                if ts.peek_word() == Some("number") {
                    ts.pos += 1;
                }
                Some(ToolKind::Whole)
            }
            Some("number") => {
                ts.pos += 1;
                Some(ToolKind::Number)
            }
            Some("decimal") => {
                ts.pos += 1;
                Some(ToolKind::Decimal)
            }
            Some("text") => {
                ts.pos += 1;
                Some(ToolKind::Text)
            }
            _ => None,
        };
        let Some(kind) = kind else {
            self.err("T0113", "A Takes or Option sentence cannot be read.".to_string(), s, 0, s.text.len(),
                "The kind after as is one of whole number, number, decimal or text, with maybe in front of it.".to_string(),
                "Write Takes file name as text.".to_string());
            return None;
        };
        Some((kind, maybe))
    }

    /// M4-G27: is the rest of the line exactly the word `input`?
    fn rest_is_input(&self, ts: &TS) -> bool {
        let mut words = 0;
        let mut pos = ts.pos;
        while pos < ts.toks.len() {
            match &ts.toks[pos] {
                Token::Word { lower, .. } => {
                    if lower != "input" || words > 0 {
                        return false;
                    }
                    words += 1;
                }
                Token::Period | Token::Eof => break,
                _ => return false,
            }
            pos += 1;
        }
        words == 1
    }

    fn parse_for(&mut self, s: &'a Sentence, sc: &mut Scope, env: &mut OwnEnv) -> Option<Stmt> {
        let (toks, _) = Lexer::new(&s.text).tokenize();
        let mut ts = TS::new(&toks);
        ts.pos += 2; // for each
        // For each x in list.  /  For each k and v in map.
        let mut vars: Vec<String> = Vec::new();
        vars.push(ts.peek_word()?.to_ascii_lowercase());
        ts.pos += 1;
        if ts.peek_word() == Some("and") {
            ts.pos += 1;
            vars.push(ts.peek_word()?.to_ascii_lowercase());
            ts.pos += 1;
        }
        if ts.peek_word() == Some("from") {
            // For each n from 1 to 5. (range loop; only one variable)
            ts.pos += 1;
            let from_toks = ts.rest_until_word("to");
            let from = self.parse_expr(from_toks, Some(s), sc, false);
            ts.consume_word("to");
            let to_toks = if !s.children.is_empty() {
                ts.rest_without_period()
            } else {
                ts.rest_until_one_line_action()
            };
            let to = self.parse_expr(to_toks, Some(s), sc, false);
            let var = vars.first()?.clone();
            let mut body_sc = sc.child();
            body_sc.define(
                &var,
                Def {
                    kind: Kind::Whole,
                    mutable: false,
                    shared: false,
                },
            );
            let body = if s.children.is_empty() {
                vec![self.parse_inline_body(ts.rest_without_period(), Some(s), &mut body_sc)]
            } else {
                self.build_block(&s.children, &mut body_sc, false, env)
            };
            Some(Stmt::ForRange {
                var,
                from,
                to,
                body,
            })
        } else if ts.peek_word() == Some("as") {
            // M4-G16 (Appendix K 7.4): For each x as they arrive from
            // CHANNEL. - the stream loop drains the channel until it closes
            // (eager cut: until the queue is empty); Stop. leaves it.
            ts.pos += 1; // as
            let a = ts.consume_word("they");
            let b = ts.consume_word("arrive");
            if !(a && b && ts.consume_word("from")) {
                self.err(
                    "T0113",
                    "A stream loop sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The stream loop reads For each x as they arrive from <a channel>.".to_string(),
                    "Write For each name as they arrive from bag.".to_string(),
                );
                return Some(Stmt::Note);
            }
            // the channel name: the words until the period
            let mut name_words: Vec<String> = Vec::new();
            while ts.pos < ts.toks.len()
                && !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof))
            {
                match ts.peek() {
                    Some(Token::Word { lower, .. }) => name_words.push(lower.to_ascii_lowercase()),
                    _ => {
                        self.err(
                            "T0113",
                            "A stream loop sentence cannot be read.".to_string(),
                            s,
                            0,
                            s.text.len(),
                            "The stream loop names one channel after from.".to_string(),
                            "Write For each name as they arrive from bag.".to_string(),
                        );
                        return Some(Stmt::Note);
                    }
                }
                ts.pos += 1;
            }
            let channel = name_words.join(" ");
            if channel.is_empty() {
                self.err(
                    "T0113",
                    "A stream loop sentence cannot be read.".to_string(),
                    s,
                    0,
                    s.text.len(),
                    "The stream loop does not name a channel.".to_string(),
                    "Write For each name as they arrive from bag.".to_string(),
                );
                return Some(Stmt::Note);
            }
            // T0168: the loop target must be a channel (the Send/Receive
            // wording is reused; deviation logged for M4-4).
            match sc.find(&channel) {
                Some(def) if matches!(def.kind, Kind::Channel(_)) => {}
                _ => {
                    self.err(
                        "T0168",
                        "For each as they arrive names a name that is not a channel.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "Only a channel can be received from in the loop.".to_string(),
                        "Define a channel of some kind, or write For each x in <a list>."
                            .to_string(),
                    );
                    return Some(Stmt::Note);
                }
            }
            let item_kind = match sc.find(&channel) {
                Some(def) => match &def.kind {
                    Kind::Channel(item) => (**item).clone(),
                    _ => Kind::Unknown,
                },
                None => Kind::Unknown,
            };
            let var = vars.first()?.clone();
            // The stream loop runs INLINE in this frame (the eager cut
            // drains in place), so a round captures names like any other
            // loop body - not the task capture rules (logged in
            // LYKAON_DEVIATIONS.md for M4-4). x is the received value, and
            // also it (M4-S13).
            let mut body_sc = sc.child();
            body_sc.define(
                &var,
                Def {
                    kind: item_kind,
                    mutable: false,
                    shared: false,
                },
            );
            let body = self.build_block(&s.children, &mut body_sc, false, env);
            Some(Stmt::StreamLoop { var, channel, body })
        } else if ts.peek_word() == Some("in") {
            // For each x in list. / For each k and v in map.
            ts.pos += 1;
            // M4-G27 (Appendix K 7.11): For each line in input. is the
            // fixed form - the variable is named line and the target is
            // the word input (the lines of standard input, M4-S85). A list
            // literally named input is read by any other variable name.
            if vars.len() == 1 && vars[0] == "line" && self.rest_is_input(&ts) {
                if s.children.is_empty() {
                    self.err(
                        "T0113",
                        "An input sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "For each line in input. needs its steps on indented lines under it."
                            .to_string(),
                        "Indent the steps under For each line in input.".to_string(),
                    );
                    return Some(Stmt::Note);
                }
                let var = vars[0].clone();
                let mut body_sc = sc.child();
                body_sc.define(
                    &var,
                    Def {
                        kind: Kind::Text,
                        mutable: false,
                        shared: false,
                    },
                );
                let body = self.build_block(&s.children, &mut body_sc, false, env);
                return Some(Stmt::ForEachInput { var, body });
            }
            // M4-G39 (Appendix K 7.5): For each x in file F. reads the
            // file one line at a time; the line is x and also it (M4-S36
            // wording: lines without their line ending).
            if matches!(ts.peek_word(), Some("file") | Some("folder")) && vars.len() == 1 {
                if s.children.is_empty() {
                    self.err(
                        "T0113",
                        "A file sentence cannot be read.".to_string(),
                        s,
                        0,
                        s.text.len(),
                        "For each <name> in file F. needs its steps on indented lines under it."
                            .to_string(),
                        "Indent the steps under For each <name> in file <name>.".to_string(),
                    );
                    return Some(Stmt::Note);
                }
                let Some(fr) = self.parse_file_ref(&mut ts, s, None) else {
                    return Some(Stmt::Note);
                };
                let var = vars[0].clone();
                let mut body_sc = sc.child();
                body_sc.define(
                    &var,
                    Def {
                        kind: Kind::Text,
                        mutable: false,
                        shared: false,
                    },
                );
                let body = self.build_block(&s.children, &mut body_sc, false, env);
                return Some(Stmt::ForEachLine {
                    var,
                    file: fr,
                    body,
                });
            }
            let list = self.parse_expr(ts.rest_without_period(), Some(s), sc, false);
            let mut body_sc = sc.child();
            for v in &vars {
                body_sc.define(
                    v,
                    Def {
                        kind: Kind::Unknown,
                        mutable: false,
                        shared: false,
                    },
                );
            }
            let body = self.build_block(&s.children, &mut body_sc, false, env);
            Some(Stmt::ForIn { vars, list, body })
        } else {
            None
        }
    }

    // ------------------------------------------------------------ say

    fn parse_say(
        &mut self,
        toks: Vec<Token>,
        s: Option<&'a Sentence>,
        sc: &mut Scope,
        literal: bool,
    ) -> Stmt {
        let lines: Vec<String> = s
            .map(|x| {
                x.children
                    .iter()
                    .map(|&c| self.all[c].text.clone())
                    .collect()
            })
            .unwrap_or_default();
        let mut ts = TS::new(&toks);
        let mut mods = SayMods::default();
        // Say if <question>. prints yes or no.
        if ts.peek_word() == Some("if") {
            ts.pos += 1;
            let cond = self.parse_condition(ts.rest_without_period(), s, sc);
            return Stmt::Say {
                expr: cond,
                mods,
                lines,
            };
        }
        loop {
            match ts.peek_word() {
                Some("literally") => {
                    mods.literally = true;
                    ts.pos += 1;
                }
                Some("lines") => {
                    ts.pos += 1;
                    return Stmt::Say {
                        expr: flat_empty(),
                        mods,
                        lines,
                    };
                }
                Some("without") => {
                    mods.without_newline = true;
                    ts.pos += 1;
                    ts.consume_word("newline");
                }
                _ => break,
            }
        }
        let (content, after) = split_trailing_mods(ts.rest_without_period());
        let expr = if mods.literally {
            flat_words(&content)
        } else if literal {
            self.parse_flat(content, sc, s, true)
        } else {
            self.parse_expr(content, s, sc, true)
        };
        let mut mts = TS::new(&after);
        if mts.consume_word("to") {
            if let Some(n) = mts.peek_number() {
                if mts.peek_next() == Some("places") || mts.peek_next() == Some("place") {
                    mods.places = Some(n as usize);
                }
            }
        } else if mts.consume_word("width") {
            if let Some(n) = mts.peek_number() {
                mods.width = Some(n as usize);
            }
        }
        Stmt::Say { expr, mods, lines }
    }

    // ------------------------------------------------------------ conditions

    fn parse_condition(&mut self, toks: Vec<Token>, s: Option<&'a Sentence>, sc: &Scope) -> Expr {
        if toks.is_empty() {
            return unknown_it();
        }
        // M4-G45 (Appendix K 7.5): wherever the sentence ends with the
        // word exists, and the rest reads as a file reference (or a name
        // bound by Make temporary file), the condition is a file exists
        // question, not a comparison.
        if let Some(Token::Word { lower: last, .. }) = toks.last() {
            if last == "exists" {
                let inner: Vec<Token> = toks[..toks.len() - 1].to_vec();
                if !inner.is_empty() {
                    let lead = match &inner[0] {
                        Token::Word { lower, .. } => Some(lower.as_str()),
                        _ => None,
                    };
                    if let Some(sentence) = s {
                        if lead == Some("file") || lead == Some("folder") {
                            if let Some(fr) = self.parse_file_ref_at(sentence, &inner, 0) {
                                return Expr {
                                    kind: Kind::Boolean,
                                    e: E::FileExists(fr),
                                    dis: String::new(),
                                    can_fail: false,
                                    num_word: false,
                                };
                            }
                        } else if inner.len() == 1 {
                            let is_word = matches!(&inner[0], Token::Word { .. });
                            if is_word {
                                let lower = match &inner[0] {
                                    Token::Word { lower, .. } => lower.clone(),
                                    _ => String::new(),
                                };
                                if self
                                    .temp_names
                                    .iter()
                                    .any(|n| n.eq_ignore_ascii_case(&lower))
                                {
                                    return Expr {
                                        kind: Kind::Boolean,
                                        e: E::FileExists(FileRef {
                                            folder: false,
                                            raw: None,
                                            temp: Some(lower),
                                            name: String::new(),
                                            ext: None,
                                            folders: Vec::new(),
                                            root: None,
                                        }),
                                        dis: String::new(),
                                        can_fail: false,
                                        num_word: false,
                                    };
                                }
                            }
                        }
                    }
                }
            }
        }
        let mut ts = TS::new(&toks);
        let mut left = self.parse_comparison(&mut ts, s, sc);
        while ts.peek_word() == Some("and") || ts.peek_word() == Some("or") {
            let is_and = ts.peek_word() == Some("and");
            ts.pos += 1;
            let right = self.parse_comparison(&mut ts, s, sc);
            left = make_and_or(left, right, is_and);
        }
        left
    }

    fn parse_comparison(&mut self, ts: &mut TS, s: Option<&'a Sentence>, sc: &Scope) -> Expr {
        let l = self.parse_operand(ts, sc, s);
        let l = self.extend_arith(l, ts, sc, s);
        // `coll has x` (Ch.12)
        if ts.peek_word() == Some("has") {
            ts.pos += 1;
            self.text_depth += 1;
            let item = self.parse_operand(ts, sc, s);
            self.text_depth -= 1;
            return boolean_cmp(Comp {
                negate: false,
                rel: Rel::Has,
                l: Box::new(l),
                r: vec![Box::new(item)],
            });
        }
        if ts.peek_word() != Some("is") {
            return unknown_it();
        }
        ts.pos += 1;
        let mut negate = false;
        if ts.peek_word() == Some("not") && ts.peek_next() != Some("between") {
            negate = true;
            ts.pos += 1;
        }
        // `coll is empty` / `coll has x` (Ch.11/12)
        if ts.peek_word() == Some("empty") {
            ts.pos += 1;
            return boolean_cmp(Comp {
                negate,
                rel: Rel::IsEmpty,
                l: Box::new(l),
                r: vec![],
            });
        }
        // `x is missing` / `x is there` (ch.18)
        if ts.peek_word() == Some("missing") {
            ts.pos += 1;
            return boolean_cmp(Comp {
                negate,
                rel: Rel::Missing,
                l: Box::new(l),
                r: vec![],
            });
        }
        if ts.peek_word() == Some("there") {
            ts.pos += 1;
            return boolean_cmp(Comp {
                negate,
                rel: Rel::There,
                l: Box::new(l),
                r: vec![],
            });
        }
        if ts.peek_word() == Some("has") {
            ts.pos += 1;
            self.text_depth += 1;
            let item = self.parse_operand(ts, sc, s);
            self.text_depth -= 1;
            return boolean_cmp(Comp {
                negate,
                rel: Rel::Has,
                l: Box::new(l),
                r: vec![Box::new(item)],
            });
        }
        // the value after is/between is a value position (Ch.4, rule 2)
        self.text_depth += 1;
        if ts.peek_word() == Some("between") {
            ts.pos += 1;
            let lo = self.parse_operand(ts, sc, s);
            ts.consume_word("and");
            let hi = self.parse_operand(ts, sc, s);
            self.text_depth -= 1;
            return boolean_cmp(Comp {
                negate,
                rel: Rel::Between,
                l: Box::new(l),
                r: vec![Box::new(lo), Box::new(hi)],
            });
        }
        let rel = match ts.peek_word() {
            Some("more") => {
                ts.pos += 1;
                ts.consume_word("than");
                Rel::More
            }
            Some("less") => {
                ts.pos += 1;
                ts.consume_word("than");
                Rel::Less
            }
            Some("at") => {
                ts.pos += 1;
                if ts.consume_word("least") {
                    Rel::AtLeast
                } else if ts.consume_word("most") {
                    Rel::AtMost
                } else {
                    Rel::Equal
                }
            }
            Some("close") => {
                ts.pos += 1;
                ts.consume_word("to");
                Rel::Close
            }
            _ => Rel::Equal,
        };
        let r = self.parse_operand(ts, sc, s);
        let r = self.extend_arith(r, ts, sc, s);
        self.text_depth -= 1;
        // T0306 (ch.66): a comparison puts two kinds together (a counter
        // or atomic compares as its whole value)
        if let Some(ss) = s {
            let unwrap = |k: &Kind| match k {
                Kind::Guarded(inner) => inner.as_ref().clone(),
                Kind::Counter | Kind::Atomic => Kind::Whole,
                k => k.clone(),
            };
            let lk = unwrap(&l.kind);
            let rk = unwrap(&r.kind);
            let comparable = |k: &Kind| !matches!(k, Kind::Unknown | Kind::Missing);
            if comparable(&lk) && comparable(&rk) && lk != rk {
                let (lo, hi) = span_of(&ss.text, &r.dis);
                self.err(
                    "T0306",
                    "Comparing different kinds.".to_string(),
                    ss,
                    lo,
                    hi,
                    "A comparison puts two kinds together.".to_string(),
                    "Use one kind.".to_string(),
                );
            }
        }
        boolean_cmp(Comp {
            negate,
            rel,
            l: Box::new(l),
            r: vec![Box::new(r)],
        })
    }

    /// Continue an operand with the arithmetic runs that parse_expr handles in
    /// value positions (Ch.4): whole divided by, rounded, factorial, plus,
    /// minus, times, divided by. Comparisons need them too ("Check that
    /// n plus 1 is 2.").
    fn extend_arith(
        &mut self,
        mut cur: Expr,
        ts: &mut TS,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Expr {
        loop {
            let (dis, cf) = (cur.dis.clone(), cur.can_fail);
            if ts.peek_word() == Some("whole") {
                ts.pos += 1;
                if ts.consume_word("divided") && ts.consume_word("by") {
                    let r = self.op_operand(ts, sc, s);
                    cur = Expr {
                        kind: Kind::Whole,
                        e: E::DivWhole(Box::new(cur), Box::new(r)),
                        dis,
                        can_fail: cf,
                        num_word: false,
                    };
                    continue;
                }
                ts.pos -= 1;
                break;
            }
            if ts.peek_word() == Some("rounded") {
                ts.pos += 1;
                let mut to_even = false;
                if ts.peek_word() == Some("to") {
                    ts.pos += 1;
                    if ts.consume_word("even") {
                        to_even = true;
                    } else {
                        ts.pos -= 1;
                    }
                }
                cur = Expr {
                    kind: Kind::Whole,
                    e: E::Round(Box::new(cur), to_even),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("factorial") {
                ts.pos += 1;
                cur = Expr {
                    kind: Kind::Big,
                    e: E::Factorial(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            match ts.peek_word().map(|w| w.to_string()) {
                Some(w) if w == "plus" || w == "minus" || w == "times" || w == "divided" => {
                    ts.pos += 1;
                    if w == "divided" {
                        ts.consume_word("by");
                        let r = self.op_operand(ts, sc, s);
                        self.check_mix(s, &cur, &r);
                        cur = Expr {
                            kind: Kind::Decimal,
                            e: E::Binary {
                                op: Op::DividedBy,
                                l: Box::new(cur),
                                r: Box::new(r),
                            },
                            dis: String::new(),
                            can_fail: cf,
                            num_word: false,
                        };
                    } else {
                        let op = match w.as_str() {
                            "plus" => Op::Plus,
                            "minus" => Op::Minus,
                            _ => Op::Time,
                        };
                        let r = self.op_operand(ts, sc, s);
                        self.check_mix(s, &cur, &r);
                        let kind = num_kind(&cur.kind, &r.kind);
                        cur = Expr {
                            kind,
                            e: E::Binary {
                                op,
                                l: Box::new(cur),
                                r: Box::new(r),
                            },
                            dis: String::new(),
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    break; // a second operation was already reported (T0109)
                }
                _ => break,
            }
        }
        cur
    }

    // ------------------------------------------------------------ expressions

    /// Parse an expression: one value, one operation. In a Say, a run of words
    /// with no operation is one text value (Ch.5).
    /// Is a record / enum construction starting here? (ch.20-21)
    /// "a person with name Maya and age 31" / "card with owner Maya" / "cash".
    fn ctor_starts(&self, toks: &[Token], sc: &Scope) -> bool {
        let w1 = match toks.first() {
            Some(Token::Word { lower, .. }) => lower.clone(),
            _ => return false,
        };
        if matches!(w1.as_str(), "a" | "an") {
            if let (Some(Token::Word { lower: t, .. }), Some(Token::Word { lower: w, .. })) =
                (toks.get(1), toks.get(2))
            {
                return w == "with" && self.record_types.contains_key(t);
            }
            return false;
        }
        // a shape word is an enum value (ch.21); it is also sc-defined, but
        // construction ("card with owner Maya.") wins over a plain read.
        // A bare shape must stand alone: more value words after it turn the
        // run into flat text ("Line is cat sat down." stays text m1 semantics
        // unless the words are names).
        if self.shape_names.contains_key(&w1) {
            let bare = match toks.get(1) {
                None => true,
                Some(Token::Word { lower, .. }) => lower == "with",
                Some(Token::Period | Token::Eof) => true,
                Some(_) => false,
            };
            if bare {
                return true;
            }
            return false;
        }
        // a defined name wins over a record type used bare
        if sc.find(&w1).is_some() {
            return false;
        }
        if self.record_types.contains_key(&w1) {
            if let Some(Token::Word { lower: w, .. }) = toks.get(1) {
                if w == "with" {
                    return true;
                }
            }
        }
        false
    }

    /// The parts of a construction: word <part>, then the value tokens run to
    /// the next " and " (or the end). "name Maya and age 31" -> two values.
    fn ctor_part_values(
        &mut self,
        ts: &mut TS,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Vec<(String, Expr)> {
        let mut given: Vec<(String, Expr)> = Vec::new();
        loop {
            let p = match ts.peek_word() {
                Some(w) => w.to_ascii_lowercase(),
                None => break,
            };
            ts.pos += 1;
            let vtoks = ts.rest_until_word("and");
            let vtoks = vtoks
                .into_iter()
                .filter(|t| !matches!(t, Token::Period))
                .collect::<Vec<_>>();
            self.text_depth += 1;
            let vexpr = self.parse_expr(vtoks, s, sc, true);
            self.text_depth -= 1;
            given.push((p, vexpr));
            if ts.peek_word() == Some("and") {
                ts.pos += 1;
                continue;
            }
            break;
        }
        given
    }

    /// Parse a record or enum construction. The words before "with" are parts,
    /// each with a value.
    fn ctor_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        let w1 = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => return self.parse_operand(ts, sc, s),
        };
        if matches!(w1.as_str(), "a" | "an") {
            ts.pos += 1;
        }
        let tname = match ts.peek_word() {
            Some(w) => w.to_ascii_lowercase(),
            None => return self.parse_operand(ts, sc, s),
        };
        ts.pos += 1;
        // a record type: a person with name Maya and age 31 (ch.20)
        let rparts = self.record_types.get(&tname).cloned();
        if let Some(rparts) = rparts {
            ts.consume_word("with");
            let given = self.ctor_part_values(ts, sc, s);
            let mut out: Vec<(String, Expr)> = Vec::new();
            for (n, k) in &rparts {
                match given.iter().find(|(g, _)| g == n) {
                    Some((_, v)) => {
                        out.push((n.clone(), v.clone()));
                        // T0309 (M2): the value written for a part must have
                        // the part's declared kind.
                        if !kind_fits(k, &v.kind) {
                            if let Some(ss) = s {
                                // point at the value written for the part when
                                // its words appear in the sentence, otherwise
                                // at the part name
                                let (a, b) = {
                                    let (a, b) = name_span(&ss.text, &v.dis);
                                    if a == b {
                                        name_span(&ss.text, n)
                                    } else {
                                        (a, b)
                                    }
                                };
                                self.err(
                                    "T0309",
                                    "Part kind differs.".to_string(),
                                    ss,
                                    a,
                                    b,
                                    "A part of a record has the wrong kind.".to_string(),
                                    "Use the declared kind.".to_string(),
                                );
                            }
                        }
                    }
                    None => {
                        if let Some(ss) = s {
                            self.err(
                                "T0313",
                                format!("A {tname} is made without a part called {n}."),
                                ss,
                                0,
                                ss.text.len(),
                                "A record is made with every part given, once each.".to_string(),
                                format!("Add {n} and its value."),
                            );
                        }
                    }
                }
                let _ = k;
            }
            for (g, _) in &given {
                if !rparts.iter().any(|(n, _)| n == g) {
                    if let Some(ss) = s {
                        self.err(
                            "T0314",
                            format!("A {tname} has no part called {g}."),
                            ss,
                            0,
                            ss.text.len(),
                            format!("A {tname} was not declared with a part {g}."),
                            format!("Use the parts of {tname}."),
                        );
                    }
                }
            }
            let kinds = rparts.iter().map(|(n, k)| (n.clone(), k.clone())).collect();
            return Expr {
                dis: format!("a {tname}"),
                kind: Kind::Record(tname.clone(), kinds),
                e: E::RecordOf {
                    type_name: tname,
                    parts: out,
                },
                can_fail: false,
                num_word: false,
            };
        }
        // a shape name: card with owner Maya / cash (ch.21)
        let shape = self.shape_names.get(&tname).cloned();
        if let Some((ename, sparts)) = shape {
            let mut given: Vec<(String, Expr)> = Vec::new();
            if ts.peek_word() == Some("with") {
                ts.pos += 1;
                given = self.ctor_part_values(ts, sc, s);
            }
            let ok = sparts.len() == given.len()
                && sparts
                    .iter()
                    .all(|(n, _)| given.iter().any(|(g, _)| g == n));
            if !ok {
                if let Some(ss) = s {
                    self.err(
                        "T0315",
                        "A variant is made with the wrong parts.".to_string(),
                        ss,
                        0,
                        ss.text.len(),
                        format!("{ename}'s {tname} is not made with its declared parts."),
                        "Use the declared parts.".to_string(),
                    );
                }
            }
            let mut out: Vec<(String, Expr)> = Vec::new();
            for (n, _) in &sparts {
                if let Some((_, v)) = given.iter().find(|(g, _)| g == n) {
                    out.push((n.clone(), v.clone()));
                }
            }
            let kind = self
                .enum_types
                .get(&ename)
                .map(|vs| Kind::Enum(vs.clone()))
                .unwrap_or(Kind::Unknown);
            return Expr {
                dis: tname.clone(),
                kind,
                e: E::EnumOf {
                    shape: tname,
                    parts: out,
                },
                can_fail: false,
                num_word: false,
            };
        }
        self.parse_operand(ts, sc, s)
    }

    /// Does the token run need the expression path? The operation words (ch.4)
    /// or a part read "X of <record>" (ch.20) do; plain words stay flat text.
    fn expr_gate(&self, toks: &[Token], sc: &Scope) -> bool {
        if has_operation_word(toks) {
            return true;
        }
        // give X / share X are operators (ch.28), never flat text
        if matches!(toks.first(), Some(Token::Word { lower, .. }) if lower == "give" || lower == "share")
        {
            return true;
        }
        // weak share X is a non-owning link (ch.28), never flat text
        if toks.len() >= 2 {
            if let [Token::Word { lower: l1, .. }, Token::Word { lower: l2, .. }] = toks {
                if l1 == "weak" && l2 == "share" {
                    return true;
                }
            }
        }
        // M4 (Appendix K): the new value constructions are never flat text.
        // channel of T [holding N] / guarded V / atomic number / counter.
        if matches!(toks.first(), Some(Token::Word { lower, .. }) if lower == "channel") {
            if toks
                .iter()
                .skip(1)
                .any(|t| w_lower(t).map(|s| s.as_str()) == Some("of"))
            {
                return true;
            }
        }
        if matches!(toks.first(), Some(Token::Word { lower, .. }) if lower == "guarded")
            && toks.len() >= 2
        {
            return true;
        }
        if matches!(toks.first(), Some(Token::Word { lower: l1, .. }) if l1 == "atomic")
            && matches!(toks.get(1), Some(Token::Word { lower: l2, .. }) if l2 == "number")
        {
            return true;
        }
        if matches!(toks.first(), Some(Token::Word { lower, .. }) if lower == "counter") {
            return true;
        }
        // M4-6 (S46): json of x is a value construction, never flat text
        if matches!(toks.first(), Some(Token::Word { lower, .. }) if lower == "json")
            && toks.len() >= 2
            && matches!(toks.get(1), Some(Token::Word { lower: l2, .. }) if l2 == "of")
        {
            return true;
        }
        // ---- M4-7 (Appendix K 7.7): the time, random and secret value
        // words are never flat text ----
        // date N and N and N / today / now
        if let Some(Token::Word { lower, .. }) = toks.first() {
            match lower.as_str() {
                "today" | "now" => return true,
                "date" => {
                    if matches!(toks.get(1), Some(Token::Whole { .. }))
                        && matches!(toks.get(2), Some(Token::Word { lower: l2, .. }) if l2 == "and")
                    {
                        return true;
                    }
                }
                "moment" => {
                    // moment of D at H and M: the "at H" part makes it a
                    // value read, so "the moment of truth" stays flat
                    let at_num = toks.windows(2).any(|w| {
                        matches!((&w[0], &w[1]),
                            (Token::Word { lower: l1, .. }, Token::Whole { .. })
                                if l1 == "at")
                    });
                    if at_num {
                        return true;
                    }
                }
                "random" => {
                    if matches!(toks.get(1), Some(Token::Word { lower: l2, .. })
                        if l2 == "number" || l2 == "decimal" || l2 == "item")
                    {
                        return true;
                    }
                }
                "hash" => {
                    if matches!(toks.get(1), Some(Token::Word { lower: l2, .. }) if l2 == "of") {
                        return true;
                    }
                }
                // secret X / reveal X are reserved value words (G60/G61)
                "secret" | "reveal" => return true,
                // days between X and Y / seconds between X and Y
                "days" | "seconds" => {
                    if matches!(toks.get(1), Some(Token::Word { lower: l2, .. }) if l2 == "between")
                    {
                        return true;
                    }
                }
                // M4-8 (7.11): read input (G27) is a value read; a flat
                // text "read" stays flat (the words after decide)
                "read" => {
                    if toks.len() >= 2
                        && matches!(toks.get(1), Some(Token::Word { lower: l2, .. }) if l2 == "input")
                        && toks.len() == 2
                    {
                        return true;
                    }
                }
                // M4-8 (7.10): Environment <names> (G24) is a value read;
                // the words after it name the variable
                "environment" => {
                    if toks.len() >= 2
                        && toks.iter().skip(1).all(|t| matches!(t, Token::Word { .. }))
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
        // NUMBER time_unit [after/before] (M4-S52/G5/G6): 5 seconds is a
        // duration value
        if let (Some(Token::Whole { .. }), Some(Token::Word { lower, .. })) =
            (toks.first(), toks.get(1))
        {
            if m4_time_unit(lower).is_some() {
                return true;
            }
        }
        // X in zone <names> (M4-G55) / X shuffled (M4-G57)
        for w in toks.windows(2) {
            if let (Some(l1), Some(l2)) = (w_lower(&w[0]), w_lower(&w[1])) {
                if l1 == "in" && l2 == "zone" {
                    return true;
                }
            }
        }
        if toks
            .iter()
            .any(|t| w_lower(t).map(|s| s.as_str()) == Some("shuffled"))
        {
            return true;
        }
        // copy of X is an owned copy (ch.20), never flat text
        for w in toks.windows(3) {
            let (Some(l1), Some(l2), Some(l3)) = (w_lower(&w[0]), w_lower(&w[1]), w_lower(&w[2]))
            else {
                continue;
            };
            if l1 == "copy" && l2 == "of" {
                return true;
            }
            if l2 == "of" && l3 != "of" {
                // the base after "of" must hold a record, and the part word
                // must not be a word that carries its own "of" structure
                if self.is_record_value_name(l3, sc) && !OF_STRUCTURE_WORDS.contains(&l1.as_str()) {
                    return true;
                }
                // M4-10 (S60): a pronoun base (it after a Fetch or a
                // Post) carries the response record one sentence back
                // (fresh_kind)
                if matches!(l3.as_str(), "it" | "them")
                    && matches!(&self.fresh_kind, Kind::Record(..))
                    && !OF_STRUCTURE_WORDS.contains(&l1.as_str())
                {
                    return true;
                }
            }
        }
        // M3 (ch.24): "biggest of X and Y" / "smallest of X and Y" are value
        // forms, never flat text. The word alone ("the biggest fish") stays flat.
        for w in toks.windows(2) {
            if let (Some(l1), Some(l2)) = (w_lower(&w[0]), w_lower(&w[1])) {
                if (l1 == "biggest" || l1 == "smallest") && l2 == "of" {
                    return true;
                }
            }
        }
        // M4-10 (7.8): a request read - "method of request", "text of
        // request", "header NAME of request" and the like - is a value
        // read inside a handler body, never flat text. The row word may
        // sit anywhere in the run and the header/query/parameter rows
        // carry name words between the row word and of.
        for i in 0..toks.len() {
            let Some(l1) = w_lower(&toks[i]) else {
                continue;
            };
            if !matches!(
                l1.as_str(),
                "method" | "page" | "text" | "data" | "header" | "query" | "parameter"
            ) {
                continue;
            }
            if i + 2 < toks.len()
                && w_lower(&toks[i + 1]).map(|s| s.as_str()) == Some("of")
                && w_lower(&toks[i + 2]).map(|s| s.as_str()) == Some("request")
            {
                return true;
            }
            if matches!(l1.as_str(), "header" | "query" | "parameter") {
                for k in (i + 1)..toks.len().saturating_sub(1) {
                    if w_lower(&toks[k]).map(|s| s.as_str()) == Some("of")
                        && w_lower(&toks[k + 1]).map(|s| s.as_str()) == Some("request")
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn is_record_value_name(&self, name: &str, sc: &Scope) -> bool {
        match sc.find(name) {
            Some(d) => match &d.kind {
                Kind::Record(..) => true,
                Kind::Maybe(inner) => matches!(**inner, Kind::Record(..)),
                _ => false,
            },
            None => false,
        }
    }

    /// "name of maya" reads a record part (ch.20). Only called when "of"
    /// follows the word; the base is parsed speculatively and the tokens are
    /// put back when the base does not hold a record.
    fn spec_part_of(
        &mut self,
        ts: &mut TS,
        part: &str,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Option<Expr> {
        if ts.peek_next() != Some("of") {
            return None;
        }
        // quick look: the word after "of" must lead to a record
        let after = match ts.toks.get(ts.pos + 2) {
            Some(Token::Word { lower, .. }) => lower.clone(),
            _ => return None,
        };
        // quick look: the word after "of" must not be a defined value of some
        // other kind (a chain middle like "home" is fine; it speculates on)
        if sc.find(&after).is_some() && !self.is_record_value_name(&after, sc) {
            return None;
        }
        let save = ts.pos;
        let saved_err = self.err_reported;
        let diag_len = self.diags.len();
        ts.pos += 2; // part word + of
        self.text_depth += 1;
        let base = self.parse_operand(ts, sc, s);
        self.text_depth -= 1;
        let (tname, rparts) = match &base.kind {
            Kind::Record(t, parts) => (t.clone(), parts.clone()),
            Kind::Maybe(inner) => match &**inner {
                Kind::Record(t, parts) => (t.clone(), parts.clone()),
                _ => {
                    ts.pos = save;
                    self.err_reported = saved_err;
                    self.diags.truncate(diag_len);
                    return None;
                }
            },
            // M4-10 (S60): it after a Fetch or a Post carries the
            // response record at run time; the compile kind is kept on
            // the builder one sentence back (fresh_kind).
            Kind::Unknown
                if matches!(base.e, E::It) && matches!(&self.fresh_kind, Kind::Record(..)) =>
            {
                match self.fresh_kind.clone() {
                    Kind::Record(t, parts) => (t, parts),
                    _ => unreachable!(),
                }
            }
            _ => {
                ts.pos = save;
                self.err_reported = saved_err;
                self.diags.truncate(diag_len);
                return None;
            }
        };
        if !rparts.iter().any(|(n, _)| n == part) {
            // the base is really a record but has no such part: a real error
            if let Some(ss) = s {
                self.err(
                    "T0314",
                    format!("A {tname} has no part called {part}."),
                    ss,
                    0,
                    ss.text.len(),
                    format!("A {tname} was not declared with a part {part}."),
                    format!("Use the parts of {tname}."),
                );
            }
            let kind = rparts
                .iter()
                .find(|(n, _)| n == part)
                .map(|(_, k)| k.clone())
                .unwrap_or(Kind::Unknown);
            return Some(Expr {
                kind,
                e: E::PartOf {
                    type_name: tname,
                    part: part.to_string(),
                    base: Box::new(base),
                },
                dis: format!("{part} of {}", "it"),
                can_fail: false,
                num_word: false,
            });
        }
        let kind = rparts
            .iter()
            .find(|(n, _)| n == part)
            .map(|(_, k)| k.clone())
            .unwrap_or(Kind::Unknown);
        let dis = format!("{part} of {}", base.dis);
        let cf = matches!(base.kind, Kind::Maybe(..)) || base.can_fail;
        Some(Expr {
            dis,
            kind,
            e: E::PartOf {
                type_name: tname,
                part: part.to_string(),
                base: Box::new(base),
            },
            can_fail: cf,
            num_word: false,
        })
    }

    fn parse_expr(
        &mut self,
        toks: Vec<Token>,
        s: Option<&'a Sentence>,
        sc: &Scope,
        in_say: bool,
    ) -> Expr {
        if toks.is_empty() {
            return flat_empty();
        }
        // Record / enum construction ("a person with ...", "card with owner ...",
        // "cash") is a value, not flat text (ch.20-21): the gate runs before the
        // flat path. A part read ("name of maya") also leaves the flat path.
        let ctor = self.ctor_starts(&toks, sc);
        if !ctor && in_say && !self.expr_gate(&toks, sc) {
            // ch.36: a name that a used module keeps private is T0208, even
            // when the run would otherwise be flat text ("Say triple 5.").
            if let (Some(ss), Some(Token::Word { text, lower })) = (s, toks.first()) {
                if let Some(m) = crate::unshared_module_of(lower) {
                    let (lo, hi) = span_of(&ss.text, text);
                    self.err(
                        "T0208",
                        format!("{lower} is not shared by {m}. Add Share {lower}. to {m}.lykaon."),
                        ss,
                        lo,
                        hi,
                        format!("{lower} belongs to module {m}, which does not share it."),
                        format!("Add Share {lower}. to {m}.lykaon, or use a shared name."),
                    );
                }
            }
            return self.parse_flat(toks, sc, s, false);
        }
        let mut ts = TS::new(&toks);
        // "Two or more items joined by make a list where a list is wanted" (ch.11):
        // 3 and 3 and 4 unique. -> a list (a literal run ended by a postfix word).
        let mut cur = if ctor {
            self.ctor_operand(&mut ts, sc, s)
        } else if self.try_and_list_head(&mut ts, sc, s) {
            self.and_list_operand(&mut ts, sc, s)
        } else {
            self.parse_operand(&mut ts, sc, s)
        };
        loop {
            // fields needed after the value moves into a wrapper
            let (dis, cf) = (cur.dis.clone(), cur.can_fail);
            // Ch.65 (Postfix words): two postfix words in a row are two
            // operations, which is T0109 - the sentence never chains
            // them silently (`numbers sorted reversed.` is an error;
            // descending is the one postfix that modifies sorted).
            if let Some(prev) = ts.pos.checked_sub(1).and_then(|p| match &ts.toks.get(p) {
                Some(Token::Word { lower, .. }) => Some(lower.to_ascii_lowercase()),
                _ => None,
            }) {
                let postfix = matches!(
                    prev.as_str(),
                    "sorted"
                        | "reversed"
                        | "unique"
                        | "trimmed"
                        | "backwards"
                        | "rounded"
                        | "fallback"
                        | "normalized"
                        | "joined"
                        | "shuffled"
                        | "descending"
                );
                let next_postfix = matches!(
                    ts.peek_word(),
                    Some(
                        "sorted"
                            | "reversed"
                            | "unique"
                            | "trimmed"
                            | "backwards"
                            | "rounded"
                            | "fallback"
                            | "normalized"
                            | "joined"
                            | "shuffled"
                    )
                );
                if postfix && next_postfix {
                    if let Some(ss) = s {
                        let (lo, hi) = span_of(
                            &ss.text,
                            &format!("{prev} {}", ts.peek_word().unwrap_or("")),
                        );
                        self.err(
                            "T0109",
                            "A sentence can hold one operation.".to_string(),
                            ss,
                            lo,
                            hi,
                            "Two postfix words in a row are two operations.".to_string(),
                            "Write each step on its own line.".to_string(),
                        );
                    }
                }
            }
            // ---- M4-7 (Appendix K 7.7) time and random postfixes -----
            // M4-S52/G5: NUMBER time_unit is a duration value; with
            // after/before (M4-G56) it is a time shift. The number must
            // be a literal (a logged parser cut) and the unit one of
            // milliseconds, seconds, minutes, hours, days, weeks (G6).
            if let E::Whole(n) = cur.e {
                if let Some(unit) = m4_time_unit(ts.peek_word().unwrap_or("")) {
                    ts.pos += 1;
                    let factor = m4_unit_nanos(unit);
                    let nanos = (n as i128).checked_mul(factor);
                    let Some(nanos) = nanos else {
                        if let Some(ss) = s {
                            self.err(
                                "T0113",
                                "The time length is out of range.".to_string(),
                                ss,
                                0,
                                ss.text.len(),
                                "A time length this large does not fit.".to_string(),
                                "Write a smaller length.".to_string(),
                            );
                        }
                        return Expr {
                            kind: Kind::Duration,
                            e: E::DurationOf { nanos: 0 },
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    };
                    let before = ts.peek_word() == Some("before");
                    if ts.peek_word() == Some("after") || before {
                        ts.pos += 1;
                        self.text_depth += 1;
                        let base = self.parse_operand(&mut ts, sc, s);
                        self.text_depth -= 1;
                        let kind = match base.kind {
                            Kind::Date => Kind::Date,
                            Kind::Moment => Kind::Moment,
                            _ => Kind::Unknown,
                        };
                        cur = Expr {
                            kind,
                            e: E::TimeShift {
                                n,
                                unit: unit.to_string(),
                                before,
                                base: Box::new(base),
                            },
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    } else {
                        cur = Expr {
                            kind: Kind::Duration,
                            e: E::DurationOf { nanos },
                            dis: format!("{n} {unit}"),
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    continue;
                }
            }
            // M4-G57: L shuffled -> the Fisher-Yates shuffled copy.
            if ts.peek_word() == Some("shuffled") {
                ts.pos += 1;
                cur = Expr {
                    kind: Kind::List(Box::new(Kind::Unknown)),
                    e: E::Shuffled {
                        list: Box::new(cur),
                    },
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            // M4-G55: M in zone <names> -> the same instant in another
            // zone. The names run to the end of the value; a name no
            // IANA zone matches is T0171 (S51).
            if ts.peek_word() == Some("in")
                && ts.toks.get(ts.pos + 1).map_or(
                    false,
                    |t| matches!(t, Token::Word { lower, .. } if lower == "zone"),
                )
            {
                ts.pos += 2; // in zone
                let names = ts.rest_without_period();
                ts.pos = ts.toks.len();
                let mut words: Vec<&str> = Vec::new();
                for t in &names {
                    if let Token::Word { text, .. } = t {
                        words.push(text.as_str());
                    }
                }
                let joined = words.join(" ");
                if lykaon_core::time4::find_zone(&joined).is_none() {
                    if let Some(ss) = s {
                        self.err(
                            "T0171",
                            "Bad path word, zone or program".to_string(),
                            ss,
                            0,
                            ss.text.len(),
                            format!("{joined} is not a time zone name."),
                            "Write an IANA zone, such as in zone asia dhaka.".to_string(),
                        );
                    }
                }
                cur = Expr {
                    kind: Kind::Moment,
                    e: E::InZone {
                        base: Box::new(cur),
                        zone: joined,
                    },
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("whole") {
                // A whole divided by B
                ts.pos += 1;
                if ts.consume_word("divided") && ts.consume_word("by") {
                    let r = self.op_operand(&mut ts, sc, s);
                    cur = Expr {
                        kind: Kind::Whole,
                        e: E::DivWhole(Box::new(cur), Box::new(r)),
                        dis,
                        can_fail: cf,
                        num_word: false,
                    };
                    continue;
                }
                ts.pos -= 1;
                break;
            }
            if ts.peek_word() == Some("rounded") {
                ts.pos += 1;
                let mut to_even = false;
                if ts.peek_word() == Some("to") {
                    ts.pos += 1;
                    if ts.consume_word("even") {
                        to_even = true;
                    } else {
                        ts.pos -= 1;
                    }
                }
                cur = Expr {
                    kind: Kind::Whole,
                    e: E::Round(Box::new(cur), to_even),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("factorial") {
                ts.pos += 1;
                cur = Expr {
                    kind: Kind::Big,
                    e: E::Factorial(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("sorted") {
                // <list> sorted. -> a list with the items in order (Ch.8);
                // "sorted descending" gives the items back to front (Ch.11)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                let ascending = if ts.peek_word() == Some("descending") {
                    ts.pos += 1;
                    false
                } else {
                    true
                };
                cur = Expr {
                    kind: cur_kind,
                    e: E::Sorted(Box::new(cur), ascending),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("reversed") {
                // <list> reversed. -> the items back to front (Ch.11)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                cur = Expr {
                    kind: cur_kind,
                    e: E::Reverse(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("unique") {
                // <set of values> unique -> the values without repeats (Ch.11)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                cur = Expr {
                    kind: cur_kind,
                    e: E::Unique(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("fallback") {
                // <maybe> fallback <default> -> the value, or the default if it is missing (Ch.18)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                self.text_depth += 1;
                let def = self.parse_operand(&mut ts, sc, s);
                self.text_depth -= 1;
                let def_kind = def.kind.clone();
                // T0312: the fallback default must match the maybe's kind
                // (ch.19: Say phone fallback hello. when phone is maybe number).
                // the cur_kind is the DECLARED kind of the name (the value's
                // own kind is the default's, not the maybe's)
                let declared_kind = match &cur.e {
                    E::Name(n) => sc
                        .find(n)
                        .map(|d| d.kind.clone())
                        .unwrap_or_else(|| cur.kind.clone()),
                    _ => cur.kind.clone(),
                };
                if let Kind::Maybe(inner) = &declared_kind {
                    if let Kind::Unknown | Kind::Missing = &**inner {
                    } else if def_kind != Kind::Unknown && def_kind != **inner {
                        if let Some(ss) = s {
                            self.err(
                                "T0312",
                                "fallback gives a different kind from the value.".to_string(),
                                ss,
                                0,
                                ss.text.len(),
                                format!("The fallback value does not match the kind of {dis}."),
                                "Use a value of the same kind.".to_string(),
                            );
                        }
                    }
                }
                cur = Expr {
                    kind: if cur_kind == Kind::Maybe(Box::new(Kind::Unknown))
                        || cur_kind == Kind::Missing
                    {
                        def_kind.clone()
                    } else {
                        cur_kind
                    },
                    e: E::Fallback {
                        value: Box::new(cur),
                        default: Box::new(def),
                    },
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("trimmed") {
                // text trimmed -> spaces removed at both ends (ch.14)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                cur = Expr {
                    kind: cur_kind,
                    e: E::Trimmed(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("backwards") {
                // text backwards -> the letters back to front, one letter at a time (ch.14)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                cur = Expr {
                    kind: cur_kind,
                    e: E::Reverse(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("normalized") {
                // text normalized -> Unicode-normalized form (ch.14)
                let cur_kind = cur.kind.clone();
                ts.pos += 1;
                cur = Expr {
                    kind: cur_kind,
                    e: E::Normalized(Box::new(cur)),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("joined") {
                // <list> joined with <word> -> text (Ch.15 defaults example)
                ts.pos += 1;
                ts.consume_word("with");
                let sep = match ts.peek_word() {
                    Some("space") => " ".to_string(),
                    Some("comma") => ",".to_string(),
                    Some("newline") => "\n".to_string(),
                    Some("tab") => "\t".to_string(),
                    Some("nothing") => String::new(),
                    Some(w) => w.to_string(),
                    None => String::new(),
                };
                if ts.peek().is_some() {
                    ts.pos += 1;
                }
                cur = Expr {
                    kind: Kind::Text,
                    e: E::JoinedWith(Box::new(cur), sep),
                    dis,
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("where") {
                // <list> where <cond> (ch.24, M3-G16): in cond, it is the item
                ts.pos += 1;
                let cond_toks = ts.rest_without_period();
                ts.pos = ts.toks.len();
                self.text_depth += 1;
                let cond = self.parse_condition(cond_toks, s, sc);
                self.text_depth -= 1;
                cur = Expr {
                    kind: Kind::List(Box::new(Kind::Unknown)),
                    e: E::Where {
                        list: Box::new(cur),
                        cond: Box::new(cond),
                    },
                    dis: dis.clone(),
                    can_fail: cf,
                    num_word: false,
                };
                continue;
            }
            if ts.peek_word() == Some("as") {
                ts.pos += 1;
                let kw = ts.peek_word().unwrap_or("").to_ascii_lowercase();
                ts.pos += 1;
                let _ = dis; // kept for the fall-through arm
                match kw.as_str() {
                    "maybe" => {
                        // A value in maybe kind (ch.18): Phone is missing as maybe number.
                        let inner = self.coll_type_word(&mut ts).unwrap_or(Kind::Unknown);
                        cur = Expr {
                            kind: Kind::Maybe(Box::new(inner)),
                            e: E::AsMaybe(Box::new(cur)),
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    "whole" => {
                        ts.consume_word("number");
                        cur = Expr {
                            kind: Kind::Whole,
                            e: E::AsWhole(Box::new(cur)),
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    "decimal" => {
                        cur = Expr {
                            kind: Kind::Decimal,
                            e: E::AsDecimal(Box::new(cur)),
                            dis,
                            can_fail: false,
                            num_word: false,
                        };
                    }
                    "big" => {
                        ts.consume_word("number");
                        cur = Expr {
                            kind: Kind::Big,
                            e: E::AsBig(Box::new(cur)),
                            dis,
                            can_fail: false,
                            num_word: false,
                        };
                    }
                    "text" => {
                        cur = Expr {
                            kind: Kind::Text,
                            e: E::AsText(Box::new(cur)),
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    "number" => {
                        cur = Expr {
                            kind: Kind::Whole,
                            e: E::AsNumber(Box::new(cur)),
                            dis,
                            can_fail: true,
                            num_word: false,
                        };
                    }
                    "any" => {
                        // as any speaker (ch.23, M3-G6): the kind is any plus
                        // the agent noun of a verb. T0158: the noun must name
                        // a declared interface (the verb or its agent noun).
                        let verb = ts.peek_word().unwrap_or("").to_ascii_lowercase();
                        ts.pos += 1;
                        let declared = self
                            .interfaces
                            .iter()
                            .any(|i| i.verb == verb || agent_noun(&i.verb) == verb);
                        if !declared {
                            if let Some(ss) = s {
                                let (a, b) = {
                                    let (a, b) = name_span(&ss.text, &verb);
                                    if a == b { (0, ss.text.len()) } else { (a, b) }
                                };
                                self.err(
                                    "T0158",
                                    "Unknown dynamic kind.".to_string(),
                                    ss,
                                    a,
                                    b,
                                    format!("any {verb} names no interface."),
                                    "Declare can fly.".to_string(),
                                );
                            }
                        }
                        cur = Expr {
                            kind: Kind::Unknown,
                            e: E::AsDyn {
                                value: Box::new(cur),
                                verb: verb.clone(),
                            },
                            dis,
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    _ => {
                        ts.pos -= 2;
                        break;
                    }
                }
                continue;
            }
            match ts.peek_word().map(|w| w.to_string()) {
                Some(w) if w == "checked" || w == "wrapping" || w == "saturating" => {
                    let mode = w.as_str();
                    ts.pos += 1;
                    let Some(opw) = ts.peek_word() else { break };
                    if !matches!(opw, "plus" | "minus" | "times") {
                        break;
                    }
                    let op = match (mode, opw) {
                        ("checked", "plus") => Op::CheckedPlus,
                        ("checked", "minus") => Op::CheckedMinus,
                        ("checked", "times") => Op::CheckedTimes,
                        ("wrapping", "plus") => Op::WrappingPlus,
                        ("wrapping", "minus") => Op::WrappingMinus,
                        ("wrapping", "times") => Op::WrappingTimes,
                        ("saturating", "plus") => Op::SaturatingPlus,
                        ("saturating", "minus") => Op::SaturatingMinus,
                        ("saturating", "times") => Op::SaturatingTimes,
                        _ => unreachable!(),
                    };
                    ts.pos += 1;
                    let r = self.op_operand(&mut ts, sc, s);
                    self.check_mix(s, &cur, &r);
                    let kind = num_kind(&cur.kind, &r.kind);
                    // checked math can fail on overflow; wrapping/saturating never do
                    let can_fail =
                        matches!(op, Op::CheckedPlus | Op::CheckedMinus | Op::CheckedTimes);
                    cur = Expr {
                        kind,
                        e: E::Binary {
                            op,
                            l: Box::new(cur),
                            r: Box::new(r),
                        },
                        dis: String::new(),
                        can_fail,
                        num_word: false,
                    };
                    break;
                }
                Some(w) if w == "plus" || w == "minus" || w == "times" || w == "divided" => {
                    ts.pos += 1;
                    if w == "divided" {
                        ts.consume_word("by");
                        let r = self.op_operand(&mut ts, sc, s);
                        self.check_mix(s, &cur, &r);
                        cur = Expr {
                            kind: Kind::Decimal,
                            e: E::Binary {
                                op: Op::DividedBy,
                                l: Box::new(cur),
                                r: Box::new(r),
                            },
                            dis: String::new(),
                            can_fail: cf,
                            num_word: false,
                        };
                    } else {
                        let op = match w.as_str() {
                            "plus" => Op::Plus,
                            "minus" => Op::Minus,
                            _ => Op::Time,
                        };
                        let r = self.op_operand(&mut ts, sc, s);
                        self.check_mix(s, &cur, &r);
                        let kind = num_kind(&cur.kind, &r.kind);
                        cur = Expr {
                            kind,
                            e: E::Binary {
                                op,
                                l: Box::new(cur),
                                r: Box::new(r),
                            },
                            dis: String::new(),
                            can_fail: cf,
                            num_word: false,
                        };
                    }
                    break; // a second operation was already reported (T0109)
                }
                _ => break,
            }
        }
        // leftover number words like "five as text" were handled in the operand
        cur
    }

    /// T0302: a whole number and a decimal in one operation (Ch.17, p.58).
    /// T0301: kinds that cannot meet.
    fn check_mix(&mut self, s: Option<&'a Sentence>, l: &Expr, r: &Expr) {
        let Some(s) = s else { return };
        let lw = l.kind == Kind::Whole;
        let ld = l.kind == Kind::Decimal;
        let rw = r.kind == Kind::Whole;
        let rd = r.kind == Kind::Decimal;
        if (lw && rd) || (ld && rw) {
            let whole_side = if lw { l.dis.clone() } else { r.dis.clone() };
            self.err("T0302",
                format!("A whole number and a decimal cannot meet in one operation. Write {whole_side} as decimal."),
                s, 0, s.text.len(),
                "A whole number and a decimal meet in one operation.".to_string(),
                format!("Write {whole_side} as decimal."));
        } else if (l.kind == Kind::Text && is_num_kind(&r.kind))
            || (is_num_kind(&l.kind) && r.kind == Kind::Text)
        {
            self.err(
                "T0301",
                "A value of one kind is used where another is needed.".to_string(),
                s,
                0,
                s.text.len(),
                "A value of one kind is used where another is needed.".to_string(),
                "Convert it with as.".to_string(),
            );
        } else if maybe_warn(l, r) || maybe_warn(r, l) {
            // a maybe value used without asking (ch.18, T0310); the book
            // example suggests a fallback of 0
            let name = if maybe_warn(l, r) {
                l.dis.clone()
            } else {
                r.dis.clone()
            };
            self.err(
                "T0310",
                format!("{name} may be missing. Ask If {name} is there, or use {name} fallback 0."),
                s,
                0,
                s.text.len(),
                format!("{name} may be missing."),
                format!("Ask If {name} is there, or use {name} fallback 0."),
            );
        }
    }

    /// A run of words with no operation: join pieces with spaces (Ch.5). A
    /// function call inside the run is still one value (Ch.15: Say double 21.).
    fn parse_flat(
        &mut self,
        toks: Vec<Token>,
        sc: &Scope,
        s: Option<&'a Sentence>,
        literal: bool,
    ) -> Expr {
        let mut ts = TS::new(&toks);
        let mut pieces: Vec<Expr> = Vec::new();
        while ts.pos < ts.toks.len() {
            match ts.peek().cloned() {
                Some(Token::Period) | Some(Token::Eof) | None => break,
                Some(Token::Whole { value }) => {
                    ts.pos += 1;
                    pieces.push(Expr {
                        kind: Kind::Whole,
                        e: E::Whole(value),
                        dis: value.to_string(),
                        can_fail: false,
                        num_word: false,
                    });
                }
                Some(Token::Decimal { value }) => {
                    ts.pos += 1;
                    pieces.push(Expr {
                        kind: Kind::Decimal,
                        e: E::Dec(value),
                        dis: lit_dec(value),
                        can_fail: false,
                        num_word: false,
                    });
                }
                Some(Token::YesNo { value }) => {
                    ts.pos += 1;
                    pieces.push(Expr {
                        kind: Kind::Boolean,
                        e: E::Boolean(value),
                        dis: String::new(),
                        can_fail: false,
                        num_word: false,
                    });
                }
                Some(Token::Negative { value }) => {
                    ts.pos += 1;
                    pieces.push(Expr {
                        kind: Kind::Whole,
                        e: E::Whole(-value),
                        dis: format!("minus {value}"),
                        can_fail: false,
                        num_word: false,
                    });
                }
                Some(Token::Missing) | Some(Token::Nothing) => {
                    ts.pos += 1;
                    pieces.push(Expr {
                        kind: Kind::Missing,
                        e: E::Missing,
                        dis: String::new(),
                        can_fail: false,
                        num_word: false,
                    });
                }
                Some(Token::Word { text, .. }) => {
                    let lower0 = text.to_ascii_lowercase();
                    if !literal && self.is_function_name(&lower0) {
                        // a call is one value: name arg [with arg]*
                        ts.pos += 1;
                        let mut args = Vec::new();
                        let next_is_arg = match ts.peek() {
                            None | Some(Token::Period) | Some(Token::Eof) => false,
                            Some(Token::Word { lower, .. }) => {
                                // "minus 2" after a call name is a negative
                                // literal argument (Ch.15: Say classify minus 2.);
                                // "minus n" is the negation of the variable
                                if lower == "minus" {
                                    matches!(
                                        ts.toks.get(ts.pos + 1),
                                        Some(Token::Whole { .. }) | Some(Token::Decimal { .. })
                                    ) || matches!(
                                        ts.toks.get(ts.pos + 1),
                                        Some(Token::Word { lower: w, .. }) if !is_op_word(w)
                                    )
                                } else {
                                    !is_op_word(lower)
                                }
                            }
                            _ => true,
                        };
                        if next_is_arg {
                            args.push(self.arg_operand(&mut ts, sc, s));
                        }
                        while ts.peek_word() == Some("with") {
                            ts.pos += 1;
                            args.push(self.arg_operand(&mut ts, sc, s));
                        }
                        // a function-name word at the end of a flat run is plain
                        // text, not a zero-argument call ("Say could not halve.")
                        if args.is_empty() && !pieces.is_empty() {
                            pieces.push(Expr {
                                kind: Kind::Text,
                                e: E::Word(text.clone()),
                                dis: text.clone(),
                                can_fail: false,
                                num_word: is_number_word(&text),
                            });
                            continue;
                        }
                        self.check_arity(&lower0, args.len(), &arg_kinds_of(&args), s);
                        let call_can_fail = self.func_can_fail(&lower0);
                        pieces.push(Expr {
                            kind: Kind::Unknown,
                            e: E::Call { name: lower0, args },
                            dis: text.clone(),
                            can_fail: call_can_fail,
                            num_word: false,
                        });
                    } else if !literal && lower0 == "it" {
                        ts.pos += 1;
                        // M4-10 (S60): it carries the fresh result's kind
                        // (the response record after a Fetch or a Post)
                        pieces.push(Expr {
                            kind: self.fresh_kind.clone(),
                            e: E::It,
                            dis: "it".to_string(),
                            can_fail: false,
                            num_word: false,
                        });
                    } else if !literal && lower0 == "them" {
                        ts.pos += 1;
                        pieces.push(Expr {
                            kind: Kind::Unknown,
                            e: E::Them,
                            dis: "them".to_string(),
                            can_fail: false,
                            num_word: false,
                        });
                    } else if !literal && let Some(n) = self.match_name_at(&mut ts, &text) {
                        self.check_ambiguous_name(&ts, &n, s);
                        let lower = n.to_ascii_lowercase();
                        let kind = sc.find(&lower).map(|d| d.kind).unwrap_or(Kind::Unknown);
                        pieces.push(Expr {
                            kind,
                            e: E::Name(lower),
                            dis: n.clone(),
                            can_fail: false,
                            num_word: false,
                        });
                    } else if !literal && let Some(d) = sc.find(&lower0) {
                        // a local name of the current scope (e.g. a For each
                        // loop variable) resolves in a flat run too
                        // T0204: a function uses a Changeable name from
                        // outside (ch.66)
                        if self.fn_outer_changeables.iter().any(|x| x == &lower0) {
                            if let Some(ss) = s {
                                let (lo, hi) = span_of(&ss.text, &text);
                                self.err(
                                    "T0204",
                                    format!(
                                        "{lower0} is a Changeable name from outside the function."
                                    ),
                                    ss,
                                    lo,
                                    hi,
                                    "A function uses a Changeable name from outside.".to_string(),
                                    "Pass it as an input.".to_string(),
                                );
                            }
                        }
                        if self.defining.as_deref() != Some(lower0.as_str()) {
                            ts.pos += 1;
                            pieces.push(Expr {
                                kind: d.kind.clone(),
                                e: E::Name(lower0),
                                dis: text.clone(),
                                can_fail: false,
                                num_word: false,
                            });
                            continue;
                        }
                        ts.pos += 1;
                        pieces.push(Expr {
                            kind: Kind::Text,
                            e: E::Word(text.clone()),
                            dis: text.clone(),
                            can_fail: false,
                            num_word: is_number_word(&text),
                        });
                    } else {
                        ts.pos += 1;
                        if !literal && is_pattern_only_word(&lower0) {
                            if let Some(ss) = s {
                                self.err("T0153", format!("{lower0} is a pattern word used outside replace, position of or split."), ss, 0, ss.text.len(),
                                    "digits, letters, optional and the like are used outside a text pattern.".to_string(),
                                    "Use them only in replace, position of or split.".to_string());
                            }
                        }
                        pieces.push(Expr {
                            kind: Kind::Text,
                            e: E::Word(text.clone()),
                            dis: text.clone(),
                            can_fail: false,
                            num_word: is_number_word(&text),
                        });
                    }
                }
            }
        }
        let e = Expr {
            kind: Kind::Text,
            e: E::Flat(pieces),
            dis: String::new(),
            can_fail: false,
            num_word: false,
        };
        Self::unwrap_single(e)
    }

    /// Collapse a flat run of one value into the value itself (a Say of a
    /// single name, or a definition like "count is 0." keeps its kind).
    fn unwrap_single(mut e: Expr) -> Expr {
        let is_one = matches!(e.e, E::Flat(ref pieces) if pieces.len() == 1);
        if is_one {
            if let E::Flat(pieces) = e.e {
                let mut pieces = pieces;
                return pieces.pop().unwrap();
            }
        }
        e
    }

    // ------------------------------------------------------------ operands

    fn parse_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        match ts.peek().cloned() {
            None | Some(Token::Period) | Some(Token::Eof) => {
                ts.pos += 1;
                unknown_it()
            }
            Some(Token::Whole { value }) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Whole,
                    e: E::Whole(value),
                    dis: value.to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::Negative { value }) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Whole,
                    e: E::Whole(-value),
                    dis: format!("minus {value}"),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::Decimal { value }) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Decimal,
                    e: E::Dec(value),
                    dis: lit_dec(value),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::YesNo { value }) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Boolean,
                    e: E::Boolean(value),
                    dis: String::new(),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::Missing) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Missing,
                    e: E::Missing,
                    dis: "missing".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::Nothing) => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Text,
                    e: E::Word("nothing".to_string()),
                    dis: "nothing".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            Some(Token::Word { text, lower }) => self.word_operand(ts, &text, &lower, sc, s),
        }
    }

    fn word_operand(
        &mut self,
        ts: &mut TS,
        text: &str,
        lower: &str,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Expr {
        match lower {
            // ch.4: the articles the/a/an are removed from code; in a
            // value position the article is transparent - the value is
            // the operand after it
            "the" | "a" | "an" => {
                ts.pos += 1;
                self.parse_operand(ts, sc, s)
            }
            "minus" => {
                ts.pos += 1;
                let inner = self.op_operand(ts, sc, s);
                let (dis, cf) = (inner.dis.clone(), inner.can_fail);
                Expr {
                    kind: Kind::Whole,
                    e: E::Neg(Box::new(inner)),
                    dis: format!("minus {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "it" => {
                ts.pos += 1;
                // M4-10 (S60): it carries the fresh result's kind
                Expr {
                    kind: self.fresh_kind.clone(),
                    e: E::It,
                    dis: "it".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "remainder" => {
                ts.pos += 1;
                ts.consume_word("of");
                let a = self.op_operand(ts, sc, s);
                ts.consume_word("by");
                let b = self.op_operand(ts, sc, s);
                Expr {
                    kind: Kind::Whole,
                    e: E::Rem(Box::new(a), Box::new(b)),
                    dis: "remainder".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "power" => {
                ts.pos += 1;
                ts.consume_word("of");
                let a = self.op_operand(ts, sc, s);
                ts.consume_word("and");
                let b = self.op_operand(ts, sc, s);
                Expr {
                    kind: Kind::Whole,
                    e: E::Pow(Box::new(a), Box::new(b)),
                    dis: "power".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "primes" => {
                if ts.peek_next() != Some("to") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // primes to N (M3-D12): the built-in sequence of primes
                ts.pos += 1;
                ts.consume_word("to");
                self.text_depth += 1;
                let n = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::List(Box::new(Kind::Whole)),
                    e: E::PrimesTo(Box::new(n)),
                    dis: "primes".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "json" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // M4-6 (S46): json of x - the compact json text of the
                // value in expression position (kind text)
                ts.pos += 2; // json of
                self.text_depth += 1;
                let v = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                let (dis, cf) = (v.dis.clone(), v.can_fail);
                Expr {
                    kind: Kind::Text,
                    e: E::JsonOf(Box::new(v)),
                    dis: format!("json of {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            // ---- M4-7 (Appendix K 7.7): time, random, secrets --------
            "date" => {
                // M4-G54: date N and N and N. The numbers are literals
                // only (a variable date is a logged parser cut); an
                // impossible date is T0620 (S50). Any other shape falls
                // back to the plain word.
                let num = |t: Option<&Token>| match t {
                    Some(Token::Whole { value }) => Some(*value),
                    _ => None,
                };
                let is_and = |t: Option<&Token>| matches!(t, Some(Token::Word { lower, .. }) if lower == "and");
                let (Some(y), true, Some(m), true, Some(d)) = (
                    num(ts.toks.get(ts.pos + 1)),
                    is_and(ts.toks.get(ts.pos + 2)),
                    num(ts.toks.get(ts.pos + 3)),
                    is_and(ts.toks.get(ts.pos + 4)),
                    num(ts.toks.get(ts.pos + 5)),
                ) else {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                };
                if !lykaon_core::time4::valid_date(y, m, d) {
                    if let Some(ss) = s {
                        self.err(
                            "T0620",
                            "Impossible date: a date is not a day that exists.".to_string(),
                            ss,
                            0,
                            ss.text.len(),
                            format!("date {y} and {m} and {d} is not a day in the calendar."),
                            "Write a day that exists, such as date 2026 and 10 and 31.".to_string(),
                        );
                    }
                }
                ts.pos += 6;
                Expr {
                    kind: Kind::Date,
                    e: E::DateCtor { y, m, d },
                    dis: format!("date {y} and {m} and {d}"),
                    can_fail: false,
                    num_word: false,
                }
            }
            "today" => {
                // M4-G54: today is the date in the local zone.
                ts.pos += 1;
                Expr {
                    kind: Kind::Date,
                    e: E::Today,
                    dis: "today".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "now" => {
                // M4-G55: now is the instant in the local zone.
                ts.pos += 1;
                Expr {
                    kind: Kind::Moment,
                    e: E::Now,
                    dis: "now".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "moment" => {
                // M4-G55: moment of D at H and M (H and M are literals -
                // a logged parser cut). Another shape falls back.
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 2; // moment of
                self.text_depth += 1;
                let base = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                let num = |t: Option<&Token>| match t {
                    Some(Token::Whole { value }) => Some(*value),
                    _ => None,
                };
                let at_h = if ts.peek_word() == Some("at") {
                    num(ts.toks.get(ts.pos + 1))
                } else {
                    None
                };
                let m = if at_h.is_some() {
                    let has_and = ts.toks.get(ts.pos + 2).map_or(
                        false,
                        |t| matches!(t, Token::Word { lower, .. } if lower == "and"),
                    );
                    if has_and {
                        num(ts.toks.get(ts.pos + 3))
                    } else {
                        None
                    }
                } else {
                    None
                };
                let (Some(h), Some(m)) = (at_h, m) else {
                    // no `at H and M`: the wrong shape (the T0113 family;
                    // logged - no book code for a malformed moment read)
                    if let Some(ss) = s {
                        self.err(
                            "T0113",
                            "moment of needs a date at an hour and a minute.".to_string(),
                            ss,
                            0,
                            ss.text.len(),
                            "moment of D at H and M takes a date, an hour and a minute."
                                .to_string(),
                            "Write moment of today at 14 and 30.".to_string(),
                        );
                    }
                    ts.pos = ts.toks.len();
                    return Expr {
                        kind: Kind::Moment,
                        e: E::MomentAt {
                            date: Box::new(base),
                            h: 0,
                            m: 0,
                        },
                        dis: "moment".to_string(),
                        can_fail: false,
                        num_word: false,
                    };
                };
                ts.pos += 4; // at H and M
                // an impossible clock value is the T0620 family (S50 owns
                // the code for the date; the hour and minute reuse it -
                // logged)
                if !(0..24).contains(&h) || !(0..60).contains(&m) {
                    if let Some(ss) = s {
                        self.err(
                            "T0620",
                            "Impossible date: a date is not a day that exists.".to_string(),
                            ss,
                            0,
                            ss.text.len(),
                            format!("The hour {h} and minute {m} do not name a time of day."),
                            "Write an hour from 0 to 23 and a minute from 0 to 59.".to_string(),
                        );
                    }
                }
                let (dis, cf) = (base.dis.clone(), base.can_fail);
                Expr {
                    kind: Kind::Moment,
                    e: E::MomentAt {
                        date: Box::new(base),
                        h,
                        m,
                    },
                    dis: format!("moment of {dis} at {h} and {m}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "days" | "seconds" => {
                // M4-G56: days between X and Y / seconds between X and Y
                // (a logged cut: minutes/hours between are not in the
                // grammar). Another shape falls back to the plain word.
                if ts.peek_next() != Some("between") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 2; // days between
                self.text_depth += 1;
                let a = self.parse_operand(ts, sc, s);
                let has_and = ts.peek_word() == Some("and");
                let b = if has_and {
                    ts.pos += 1;
                    Some(self.parse_operand(ts, sc, s))
                } else {
                    None
                };
                self.text_depth -= 1;
                let Some(b) = b else {
                    if let Some(ss) = s {
                        self.err(
                            "T0113",
                            format!("{lower} between needs two operands joined by and."),
                            ss,
                            0,
                            ss.text.len(),
                            format!("{lower} between X and Y takes two time values."),
                            format!("Write {lower} between d1 and d2."),
                        );
                    }
                    let e = if lower == "days" {
                        E::DaysBetween {
                            a: Box::new(a),
                            b: Box::new(unknown_it()),
                        }
                    } else {
                        E::SecondsBetween {
                            a: Box::new(a),
                            b: Box::new(unknown_it()),
                        }
                    };
                    return Expr {
                        kind: Kind::Whole,
                        e,
                        dis: lower.to_string(),
                        can_fail: false,
                        num_word: false,
                    };
                };
                let (dis, cf) = (a.dis.clone(), a.can_fail);
                let e = if lower == "days" {
                    E::DaysBetween {
                        a: Box::new(a),
                        b: Box::new(b),
                    }
                } else {
                    E::SecondsBetween {
                        a: Box::new(a),
                        b: Box::new(b),
                    }
                };
                Expr {
                    kind: Kind::Whole,
                    e,
                    dis: format!("{lower} between {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "random" => {
                // M4-G57: random number from A to B / random decimal /
                // random item of L. Another shape falls back (flat text).
                let next = ts.peek_next().unwrap_or("").to_string();
                let pick = match next.as_str() {
                    "number" | "decimal" | "item" => next,
                    _ => return self.plain_word_operand(ts, text, lower, sc, s),
                };
                ts.pos += 2; // random <pick>
                match pick.as_str() {
                    "number" => {
                        let ok_from = ts.consume_word("from");
                        self.text_depth += 1;
                        let a = self.parse_operand(ts, sc, s);
                        let ok_to = if ts.peek_word() == Some("to") {
                            ts.pos += 1;
                            true
                        } else {
                            false
                        };
                        let b = self.parse_operand(ts, sc, s);
                        self.text_depth -= 1;
                        if !ok_from || !ok_to {
                            if let Some(ss) = s {
                                self.err(
                                    "T0113",
                                    "random number needs from and to.".to_string(),
                                    ss,
                                    0,
                                    ss.text.len(),
                                    "random number from A to B takes two whole numbers."
                                        .to_string(),
                                    "Write random number from 1 to 10.".to_string(),
                                );
                            }
                        }
                        Expr {
                            kind: Kind::Whole,
                            e: E::RandomRange {
                                a: Box::new(a),
                                b: Box::new(b),
                            },
                            dis: "random number".to_string(),
                            can_fail: false,
                            num_word: false,
                        }
                    }
                    "decimal" => Expr {
                        kind: Kind::Decimal,
                        e: E::RandomDec,
                        dis: "random decimal".to_string(),
                        can_fail: false,
                        num_word: false,
                    },
                    _ => {
                        // random item of L
                        let ok_of = ts.consume_word("of");
                        self.text_depth += 1;
                        let l = self.parse_operand(ts, sc, s);
                        self.text_depth -= 1;
                        if !ok_of {
                            if let Some(ss) = s {
                                self.err(
                                    "T0113",
                                    "random item needs of.".to_string(),
                                    ss,
                                    0,
                                    ss.text.len(),
                                    "random item of L takes a collection.".to_string(),
                                    "Write random item of the words.".to_string(),
                                );
                            }
                        }
                        Expr {
                            kind: Kind::Unknown,
                            e: E::RandomItem { list: Box::new(l) },
                            dis: "random item".to_string(),
                            can_fail: false,
                            num_word: false,
                        }
                    }
                }
            }
            "hash" => {
                // M4-G59: hash of X is the SHA-256 text (64 lower-case
                // hex digits). Another shape falls back.
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 2; // hash of
                self.text_depth += 1;
                let v = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                let (dis, cf) = (v.dis.clone(), v.can_fail);
                Expr {
                    kind: Kind::Text,
                    e: E::HashOf(Box::new(v)),
                    dis: format!("hash of {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "secret" => {
                // M4-G60: secret X. The book allows text or bytes; bytes
                // are not values in this cut, so a non-text operand is
                // refused when its kind is known (T0113, logged).
                // A trailing "secret" with no operand after it is a plain
                // word (a clause value like with header token secret).
                if !matches!(
                    ts.toks.get(ts.pos + 1),
                    Some(Token::Word { .. }) | Some(Token::Whole { .. })
                ) {
                    ts.pos += 1;
                    return Expr {
                        kind: Kind::Text,
                        e: E::Word("secret".to_string()),
                        dis: "secret".to_string(),
                        can_fail: false,
                        num_word: false,
                    };
                }
                ts.pos += 1;
                self.text_depth += 1;
                let v = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                if !matches!(v.kind, Kind::Text | Kind::Unknown) {
                    if let Some(ss) = s {
                        self.err(
                            "T0113",
                            "A secret holds text (bytes are not values yet).".to_string(),
                            ss,
                            0,
                            ss.text.len(),
                            "secret T takes text (or bytes in the book).".to_string(),
                            "Write secret name.".to_string(),
                        );
                    }
                }
                let inner = Box::new(v.kind.clone());
                let (dis, cf) = (v.dis.clone(), v.can_fail);
                Expr {
                    kind: Kind::Secret(inner),
                    e: E::SecretOf(Box::new(v)),
                    dis: format!("secret {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "reveal" => {
                // M4-G61: reveal X gives the text (or bytes) of a secret.
                ts.pos += 1;
                self.text_depth += 1;
                let v = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                let inner = match &v.kind {
                    Kind::Secret(k) => (**k).clone(),
                    Kind::Unknown => Kind::Unknown,
                    _ => {
                        if let Some(ss) = s {
                            self.err(
                                "T0113",
                                "reveal takes a secret.".to_string(),
                                ss,
                                0,
                                ss.text.len(),
                                "reveal X gives the text of the secret X.".to_string(),
                                "Write reveal pass.".to_string(),
                            );
                        }
                        Kind::Unknown
                    }
                };
                let (dis, cf) = (v.dis.clone(), v.can_fail);
                Expr {
                    kind: inner,
                    e: E::Reveal(Box::new(v)),
                    dis: format!("reveal {dis}"),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "read" => {
                // M4-G27 (Appendix K 7.11): read input is all of standard
                // input as text (M4-S85). Another shape falls back to the
                // plain word.
                if !(ts.peek_next() == Some("input") && ts.toks.len() - ts.pos == 2) {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 2; // read input
                Expr {
                    kind: Kind::Text,
                    e: E::ReadInput,
                    dis: "read input".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "environment" => {
                // M4-G24 (Appendix K 7.10): Environment <names> reads the
                // variable named by the words in upper case joined by _
                // (Lykaon_MODE); it gives maybe text (M4-S80). The name's
                // words run to the end of the value (the in zone
                // reservation shape - logged).
                ts.pos += 1;
                let mut name_words: Vec<String> = Vec::new();
                let mut bad = false;
                while let Some(w) = ts.peek_word() {
                    let w = w.to_ascii_lowercase();
                    let first_ok = w
                        .chars()
                        .next()
                        .map(|c| c.is_ascii_alphabetic() || c == '_')
                        .unwrap_or(false);
                    let rest_ok = w.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
                    if !first_ok || !rest_ok {
                        bad = true;
                        break;
                    }
                    name_words.push(w.to_ascii_uppercase());
                    ts.pos += 1;
                }
                // only words may carry the name (a number in the name is
                // the wrong shape, T0113)
                if !bad && ts.pos < ts.toks.len() {
                    bad = !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None);
                }
                if bad || name_words.is_empty() {
                    if let Some(ss) = s {
                        self.err("T0113", "An Environment sentence cannot be read.".to_string(),
                            ss, 0, ss.text.len(),
                            "Environment names a variable with words that spell it: letters, digits and _, starting with a letter.".to_string(),
                            "Write Environment lykaon mode.".to_string());
                    }
                    ts.pos = ts.toks.len();
                    return Expr {
                        kind: Kind::Maybe(Box::new(Kind::Text)),
                        e: E::Environment {
                            name: String::new(),
                        },
                        dis: "environment".to_string(),
                        can_fail: false,
                        num_word: false,
                    };
                }
                Expr {
                    kind: Kind::Maybe(Box::new(Kind::Text)),
                    e: E::Environment {
                        name: name_words.join("_"),
                    },
                    dis: format!("environment {}", name_words.join(" ").to_ascii_lowercase()),
                    can_fail: false,
                    num_word: false,
                }
            }
            "biggest" | "smallest" => {
                // biggest of X and Y and ... (ch.8, M3-D15)
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 2; // biggest of
                let mut items = Vec::new();
                self.text_depth += 1;
                loop {
                    let it = self.parse_operand(ts, sc, s);
                    let it = self.extend_arith(it, ts, sc, s);
                    items.push(it);
                    if ts.consume_word("and") {
                        continue;
                    }
                    break;
                }
                self.text_depth -= 1;
                let big = lower == "biggest";
                Expr {
                    kind: Kind::Unknown,
                    e: E::MinMax { big, items },
                    dis: if big {
                        "biggest".to_string()
                    } else {
                        "smallest".to_string()
                    },
                    can_fail: false,
                    num_word: false,
                }
            }
            "rounded" => {
                ts.pos += 1;
                let inner = self.op_operand(ts, sc, s);
                Expr {
                    kind: Kind::Whole,
                    e: E::Round(Box::new(inner), false),
                    dis: text.to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "how" => {
                ts.pos += 1;
                ts.consume_word("many");
                ts.consume_word("in");
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Whole,
                    e: E::CountIn(Box::new(inner)),
                    dis: "how many".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "upper" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Text,
                    e: E::Upper(Box::new(inner)),
                    dis: "upper".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "lower" => {
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Text,
                    e: E::Lower(Box::new(inner)),
                    dis: "lower".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "them" => {
                ts.pos += 1;
                Expr {
                    kind: Kind::Unknown,
                    e: E::Them,
                    dis: "them".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "copy" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("of");
                let inner = self.parse_operand(ts, sc, s);
                let (dis, cf, kind) = (
                    format!("copy of {}", inner.dis),
                    inner.can_fail,
                    inner.kind.clone(),
                );
                Expr {
                    dis,
                    kind,
                    e: E::CopyOf(Box::new(inner)),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "give" => {
                if self.text_depth == 0 {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                let inner = self.op_operand(ts, sc, s);
                let (dis, cf, kind) = (
                    format!("give {}", inner.dis),
                    inner.can_fail,
                    inner.kind.clone(),
                );
                Expr {
                    dis,
                    kind,
                    e: E::Move(Box::new(inner)),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "share" => {
                // share X makes a counted handle; a share handle is a move kind (ch.28, M2-S3)
                ts.pos += 1;
                let inner = self.op_operand(ts, sc, s);
                let (dis, cf, kind) = (format!("share {}", inner.dis), inner.can_fail, Kind::Share);
                Expr {
                    dis,
                    kind,
                    e: E::Share(Box::new(inner)),
                    can_fail: cf,
                    num_word: false,
                }
            }
            "weak" => {
                if ts.peek_next() != Some("share") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("share");
                // a weak link does not keep its owner alive; reading it yields
                // missing once the owner is gone (ch.28, M2-S44)
                let inner = self.op_operand(ts, sc, s);
                let _ = inner;
                Expr {
                    kind: Kind::WeakShare,
                    e: E::WeakShare(Box::new(inner)),
                    dis: "weak share".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            // ---- M4 (Appendix K): channel / guarded / atomic / counter ----
            "channel" => {
                // channel of T [holding N] (M4-G7)
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("of");
                let item = match self.coll_type_word(ts) {
                    Some(k) => k,
                    None => return self.plain_word_operand(ts, text, lower, sc, s),
                };
                let mut cap: usize = 64; // M4-S11: holds at most 64 unless holding N
                if ts.peek_word() == Some("holding") {
                    ts.pos += 1;
                    match ts.peek().cloned() {
                        Some(Token::Whole { value }) if value >= 1 && value <= 1_000_000 => {
                            ts.pos += 1;
                            cap = value as usize;
                        }
                        _ => {
                            // outside the 1..1,000,000 window (M4-S11):
                            // no book code lists this shape
                            if let Some(ss) = s {
                                self.err(
                                    "T0113",
                                    "A channel sentence cannot be read.".to_string(),
                                    ss,
                                    0,
                                    ss.text.len(),
                                    "holding needs a number from 1 to 1000000.".to_string(),
                                    "Write channel of <kind> holding 16.".to_string(),
                                );
                            }
                        }
                    }
                }
                Expr {
                    kind: Kind::Channel(Box::new(item.clone())),
                    e: E::ChannelOf { item, cap },
                    dis: "channel".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "guarded" => {
                // guarded V (M4-G8): a guarded value holding V (M4-S16)
                ts.pos += 1;
                let inner = self.op_operand(ts, sc, s);
                let k = inner.kind.clone();
                Expr {
                    kind: Kind::Guarded(Box::new(k)),
                    e: E::GuardedOf(Box::new(inner)),
                    dis: format!("guarded {text}"),
                    can_fail: false,
                    num_word: false,
                }
            }
            "atomic" => {
                // atomic number (M4-G9): starts at 0 (M4-S19)
                if ts.peek_next() != Some("number") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("number");
                Expr {
                    kind: Kind::Atomic,
                    e: E::AtomicNum,
                    dis: "atomic number".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "counter" => {
                // counter (M4-G10): an atomic whole number, starts at 0 (M4-S20)
                ts.pos += 1;
                Expr {
                    kind: Kind::Counter,
                    e: E::CounterZero,
                    dis: "counter".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "list" => {
                // list of A and B and C (value position)
                ts.pos += 1;
                ts.consume_word("of");
                // `list of nothing` is the empty list (the nothing names
                // the element that is not there, M4-S73's connection bag
                // starts this way)
                if matches!(ts.peek(), Some(Token::Nothing))
                    && matches!(
                        ts.toks.get(ts.pos + 1),
                        Some(Token::Period) | Some(Token::Eof) | None
                    )
                {
                    ts.pos += 1;
                    return Expr {
                        kind: Kind::List(Box::new(Kind::Missing)),
                        e: E::ListOf(Vec::new()),
                        dis: "list".to_string(),
                        can_fail: false,
                        num_word: false,
                    };
                }
                self.text_depth += 1;
                let mut items = Vec::new();
                while !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof) | None) {
                    items.push(self.parse_operand(ts, sc, s));
                    if ts.peek_word() == Some("and") {
                        ts.pos += 1;
                    } else {
                        break;
                    }
                }
                self.text_depth -= 1;
                // element kind of the list literal, when all items agree
                let elem = items
                    .iter()
                    .map(|e| e.kind.clone())
                    .reduce(|a, b| if a == b { a } else { Kind::Unknown })
                    .unwrap_or(Kind::Unknown);
                // T0307 (ch.11): a list holds items of different kinds -
                // the scalar kinds; mixed record kinds have no static element kind
                // (the m3 conformance's dog/cat list) and are allowed
                let scalar = |k: &Kind| {
                    matches!(
                        k,
                        Kind::Whole | Kind::Decimal | Kind::Text | Kind::Boolean | Kind::Letter
                    )
                };
                let first_kind = items.first().map(|e| e.kind.clone());
                if let Some(first) = &first_kind {
                    if scalar(first)
                        && items[1..]
                            .iter()
                            .any(|e| scalar(&e.kind) && e.kind != *first)
                    {
                        if let Some(ss) = s {
                            let (lo, hi) = span_of(&ss.text, "list");
                            self.err(
                                "T0307",
                                "List items differ in kind.".to_string(),
                                ss,
                                lo,
                                hi,
                                "A list holds items of different kinds.".to_string(),
                                "Use one kind.".to_string(),
                            );
                        }
                    }
                }
                Expr {
                    kind: Kind::List(Box::new(elem)),
                    e: E::ListOf(items),
                    dis: "list".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "pair" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let a = self.parse_operand(ts, sc, s);
                let b = if ts.peek_word() == Some("and") {
                    ts.pos += 1;
                    Box::new(self.parse_operand(ts, sc, s))
                } else {
                    Box::new(Expr {
                        kind: Kind::Missing,
                        e: E::Missing,
                        dis: String::new(),
                        can_fail: false,
                        num_word: false,
                    })
                };
                self.text_depth -= 1;
                let ak = a.kind.clone();
                let bk = b.kind.clone();
                Expr {
                    kind: Kind::Pair(Box::new(ak), Box::new(bk)),
                    e: E::PairOf(Box::new(a), b),
                    dis: "pair".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "items" => {
                // items A to B of list (ch.11)
                let is_num = ts
                    .toks
                    .get(ts.pos + 1)
                    .map(|t| matches!(t, Token::Whole { .. }))
                    .unwrap_or(false);
                let has_to = matches!(ts.toks.get(ts.pos + 2), Some(Token::Word { lower, .. }) if lower == "to");
                if !(is_num && has_to) {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                let from_n = match ts.peek() {
                    Some(Token::Whole { value }) => {
                        let v = *value;
                        ts.pos += 1;
                        v as i64
                    }
                    _ => return self.plain_word_operand(ts, text, lower, sc, s),
                };
                if ts.peek_word() != Some("to") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                self.text_depth += 1;
                let from = Box::new(self.whole_expr(from_n));
                let to_val = self.parse_operand(ts, sc, s);
                ts.consume_word("of");
                self.text_depth += 1;
                let list = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::List(Box::new(Kind::Unknown)),
                    e: E::ItemsRange {
                        list: Box::new(list),
                        from,
                        to: Box::new(to_val),
                    },
                    dis: "items".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "first" => {
                let nxt = ts.peek_next();
                let is_num = ts
                    .toks
                    .get(ts.pos + 1)
                    .map(|t| matches!(t, Token::Whole { .. }))
                    .unwrap_or(false);
                if nxt != Some("of") && !is_num {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                if let Some(Token::Whole { value }) = ts.peek() {
                    // first N of list
                    let v = *value;
                    ts.pos += 1;
                    if ts.peek_word() != Some("of") {
                        // first N fibonacci (M3-D12): the built-in sequence
                        if ts.peek_word() == Some("fibonacci") {
                            ts.pos += 1;
                            return Expr {
                                kind: Kind::List(Box::new(Kind::Whole)),
                                e: E::FirstFib(Box::new(self.whole_expr(v))),
                                dis: "first".to_string(),
                                can_fail: false,
                                num_word: false,
                            };
                        }
                        return self.plain_word_operand(ts, text, lower, sc, s);
                    }
                    ts.consume_word("of");
                    self.text_depth += 1;
                    let list = self.parse_operand(ts, sc, s);
                    self.text_depth -= 1;
                    Expr {
                        kind: Kind::List(Box::new(Kind::Unknown)),
                        e: E::FirstN {
                            list: Box::new(list),
                            n: Box::new(self.whole_expr(v)),
                        },
                        dis: "first".to_string(),
                        can_fail: false,
                        num_word: false,
                    }
                } else {
                    ts.consume_word("of");
                    self.text_depth += 1;
                    let inner = self.parse_operand(ts, sc, s);
                    self.text_depth -= 1;
                    Expr {
                        kind: Kind::Unknown,
                        e: E::FirstOf(Box::new(inner)),
                        dis: "first".to_string(),
                        can_fail: false,
                        num_word: false,
                    }
                }
            }
            "second" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Unknown,
                    e: E::SecondOf(Box::new(inner)),
                    dis: "second".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "joined" => {
                if ts.peek_next() != Some("with") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // X joined with <word>: the separator is the word as text
                ts.pos += 1;
                ts.consume_word("with");
                let sep = match ts.peek_word() {
                    Some("space") => " ".to_string(),
                    Some("comma") => ",".to_string(),
                    Some("newline") => "\n".to_string(),
                    Some("tab") => "\t".to_string(),
                    Some("nothing") => String::new(),
                    Some(w) => w.to_string(),
                    None => String::new(),
                };
                if ts.peek().is_some() {
                    ts.pos += 1;
                }
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Text,
                    e: E::JoinedWith(Box::new(inner), sep),
                    dis: text.to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "item" => {
                // item N of list / safe item N of list / items A to B of list
                // Guard: need "item [safe] <number> ..." otherwise treat as a word.
                let after_item = ts.peek_next();
                let is_safe = after_item == Some("safe");
                let num_idx = if is_safe { ts.pos + 2 } else { ts.pos + 1 };
                let has_num = ts
                    .toks
                    .get(num_idx)
                    .map(|t| matches!(t, Token::Whole { .. }))
                    .unwrap_or(false);
                if !has_num {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                ts.pos += 1; // item
                let safe = is_safe;
                if safe {
                    ts.pos += 1; // safe
                }
                let n = match ts.peek() {
                    Some(Token::Whole { value }) => {
                        let v = *value;
                        ts.pos += 1;
                        v as i64
                    }
                    _ => return self.plain_word_operand(ts, text, lower, sc, s),
                };
                // T0123: lists count from 1 (ch.11)
                if n == 0 {
                    if let Some(ss) = s {
                        let (lo, hi) = span_of(&ss.text, &text);
                        self.err(
                            "T0123",
                            "Item 0.".to_string(),
                            ss,
                            lo,
                            hi,
                            "item 0 is written, but lists count from 1.".to_string(),
                            "Count from 1.".to_string(),
                        );
                    }
                }
                if ts.peek_word() == Some("to") {
                    // items A to B of list
                    ts.pos += 1;
                    self.text_depth += 1;
                    let from = Box::new(self.whole_expr(n));
                    let to_val = self.parse_operand(ts, sc, s);
                    ts.consume_word("of");
                    self.text_depth += 1;
                    let list = self.parse_operand(ts, sc, s);
                    self.text_depth -= 1;
                    Expr {
                        kind: Kind::List(Box::new(Kind::Unknown)),
                        e: E::ItemsRange {
                            list: Box::new(list),
                            from,
                            to: Box::new(to_val),
                        },
                        dis: "items".to_string(),
                        can_fail: false,
                        num_word: false,
                    }
                } else {
                    if ts.peek_word() != Some("of") {
                        return self.plain_word_operand(ts, text, lower, sc, s);
                    }
                    ts.consume_word("of");
                    self.text_depth += 1;
                    let list = self.parse_operand(ts, sc, s);
                    self.text_depth -= 1;
                    let n_expr = Box::new(self.whole_expr(n));
                    if safe {
                        Expr {
                            kind: Kind::Maybe(Box::new(Kind::Unknown)),
                            e: E::SafeItemN {
                                list: Box::new(list),
                                n: n_expr,
                            },
                            dis: "safe item".to_string(),
                            can_fail: false,
                            num_word: false,
                        }
                    } else {
                        Expr {
                            kind: Kind::Unknown,
                            e: E::ItemN {
                                list: Box::new(list),
                                n: n_expr,
                            },
                            dis: "item".to_string(),
                            can_fail: false,
                            num_word: false,
                        }
                    }
                }
            }
            "last" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // last of list
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let inner = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Unknown,
                    e: E::LastOf(Box::new(inner)),
                    dis: "last".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "position" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // position of x in list / position of x in text / position of PATTERN in text
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let needle = self.pattern_or_operand(ts, sc, s);
                self.text_depth -= 1;
                ts.consume_word("in");
                self.text_depth += 1;
                let haystack = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Maybe(Box::new(Kind::Whole)),
                    e: E::PositionOf {
                        haystack: Box::new(haystack),
                        needle: Box::new(needle),
                    },
                    dis: "position".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "value" => {
                if ts.peek_next() != Some("of") {
                    return self.plain_word_operand(ts, text, lower, sc, s);
                }
                // value of k in map
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let key = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                ts.consume_word("in");
                self.text_depth += 1;
                let map = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Maybe(Box::new(Kind::Unknown)),
                    e: E::ValueOf {
                        map: Box::new(map),
                        key: Box::new(key),
                    },
                    dis: "value".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "union" | "overlap" | "difference" => {
                // union / overlap / difference of A and B
                let op = lower;
                ts.pos += 1;
                ts.consume_word("of");
                self.text_depth += 1;
                let a = self.parse_operand(ts, sc, s);
                ts.consume_word("and");
                let b = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                let e = match op {
                    "union" => E::Union {
                        a: Box::new(a),
                        b: Box::new(b),
                    },
                    "overlap" => E::Overlap {
                        a: Box::new(a),
                        b: Box::new(b),
                    },
                    _ => E::Difference {
                        a: Box::new(a),
                        b: Box::new(b),
                    },
                };
                Expr {
                    kind: Kind::Set(Box::new(Kind::Unknown)),
                    e,
                    dis: op.to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "split" => {
                // split text at SEP (text or pattern, ch.14)
                ts.pos += 1;
                self.text_depth += 1;
                let text = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                ts.consume_word("at");
                self.text_depth += 1;
                let sep = self.pattern_or_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::List(Box::new(Kind::Text)),
                    e: E::Split {
                        text: Box::new(text),
                        sep: Box::new(sep),
                    },
                    dis: "split".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            "replace" => {
                // replace PATTERN with REPL in TEXT
                ts.pos += 1;
                self.text_depth += 1;
                let pat = self.pattern_or_operand(ts, sc, s);
                self.text_depth -= 1;
                ts.consume_word("with");
                self.text_depth += 1;
                let repl = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                ts.consume_word("in");
                self.text_depth += 1;
                let text = self.parse_operand(ts, sc, s);
                self.text_depth -= 1;
                Expr {
                    kind: Kind::Text,
                    e: E::Replace {
                        pat: Box::new(pat),
                        repl: Box::new(repl),
                        text: Box::new(text),
                    },
                    dis: "replace".to_string(),
                    can_fail: false,
                    num_word: false,
                }
            }
            _ => self.plain_word_operand(ts, text, lower, sc, s),
        }
    }

    /// A whole-number literal expression.
    fn whole_expr(&self, n: i64) -> Expr {
        Expr {
            kind: Kind::Whole,
            e: E::Whole(n),
            dis: n.to_string(),
            can_fail: false,
            num_word: false,
        }
    }

    /// In a pattern hole (replace / position of / split): a run of pattern
    /// words when they are present, else a plain operand (ch.14, M2-G30).
    fn pattern_or_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        if ts.peek_word().map(pattern_word_starts).unwrap_or(false) {
            self.pattern_operand(ts, sc, s)
        } else {
            self.parse_operand(ts, sc, s)
        }
    }

    fn pattern_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        let parts = self.parse_pattern_parts(ts, sc, s);
        Expr {
            kind: Kind::Text,
            e: E::PatWords { parts },
            dis: "pattern".to_string(),
            can_fail: false,
            num_word: false,
        }
    }

    /// pattern_part = digits | letters | spaces | anything | TEXT_WORD
    /// | (one or more pattern_part) | (optional pattern_part)
    /// | (starts with TEXT_WORD) | (ends with TEXT_WORD)
    fn parse_pattern_parts(
        &mut self,
        ts: &mut TS,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Vec<Pat> {
        let _ = (sc, s);
        let mut parts: Vec<Pat> = Vec::new();
        loop {
            let word = ts.peek_word().map(|w| w.to_string()).unwrap_or_default();
            if word.is_empty() && ts.peek().is_none() {
                break;
            }
            match word.as_str() {
                "digits" => {
                    ts.pos += 1;
                    parts.push(Pat::Digits);
                }
                "letters" => {
                    ts.pos += 1;
                    parts.push(Pat::Letters);
                }
                "spaces" => {
                    ts.pos += 1;
                    parts.push(Pat::Spaces);
                }
                "anything" => {
                    ts.pos += 1;
                    parts.push(Pat::Anything);
                }
                "one" => {
                    // one or more <part>
                    let save = ts.pos;
                    ts.pos += 1;
                    if ts.peek_word() == Some("or") {
                        ts.pos += 1;
                        if ts.peek_word() == Some("more") {
                            ts.pos += 1;
                            let inner = self.parse_pattern_part(ts);
                            if let Some(p) = inner {
                                parts.push(Pat::OneOrMore(Box::new(p)));
                                continue;
                            }
                        }
                    }
                    ts.pos = save;
                    ts.pos += 1; // "one" as a plain word
                    parts.push(Pat::Word("one".to_string()));
                }
                "optional" => {
                    ts.pos += 1;
                    let inner = self.parse_pattern_part(ts);
                    parts.push(Pat::Optional(Box::new(
                        inner.unwrap_or(Pat::Word(String::new())),
                    )));
                }
                "starts" | "ends" => {
                    let is_start = word == "starts";
                    ts.pos += 1;
                    ts.consume_word("with");
                    let next_w = ts.peek_word().map(|w| w.to_string()).unwrap_or_default();
                    if ts.peek().is_some() {
                        ts.pos += 1;
                    }
                    parts.push(if is_start {
                        Pat::StartsWith(Box::new(Pat::Word(next_w)))
                    } else {
                        Pat::EndsWith(Box::new(Pat::Word(next_w)))
                    });
                }
                "with" | "in" | "at" => break, // syntax follows
                _ => {
                    ts.pos += 1;
                    // two word parts in a row are one literal joined by a space
                    if let Some(Pat::Word(prev)) = parts.last_mut() {
                        prev.push(' ');
                        prev.push_str(&word);
                    } else {
                        parts.push(Pat::Word(word));
                    }
                }
            }
        }
        parts
    }

    /// One pattern_part after a quantifier (one or more / optional).
    fn parse_pattern_part(&mut self, ts: &mut TS) -> Option<Pat> {
        let word = ts.peek_word().map(|w| w.to_string()).unwrap_or_default();
        if word.is_empty() && ts.peek().is_none() {
            return None;
        }
        match word.as_str() {
            "digits" => {
                ts.pos += 1;
                Some(Pat::Digits)
            }
            "letters" => {
                ts.pos += 1;
                Some(Pat::Letters)
            }
            "spaces" => {
                ts.pos += 1;
                Some(Pat::Spaces)
            }
            "anything" => {
                ts.pos += 1;
                Some(Pat::Anything)
            }
            "optional" => {
                ts.pos += 1;
                Some(Pat::Optional(Box::new(self.parse_pattern_part(ts)?)))
            }
            "one" => {
                let save = ts.pos;
                ts.pos += 1;
                if ts.peek_word() == Some("or") {
                    ts.pos += 1;
                    if ts.peek_word() == Some("more") {
                        ts.pos += 1;
                        if let Some(p) = self.parse_pattern_part(ts) {
                            return Some(Pat::OneOrMore(Box::new(p)));
                        }
                    }
                }
                ts.pos = save;
                None
            }
            _ => {
                ts.pos += 1;
                Some(Pat::Word(word))
            }
        }
    }

    /// Does the stream start with `literal and literal ...` ended by a postfix
    /// word (sorted / reversed / unique)? Then the run is a list (ch.11).
    fn try_and_list_head(&self, ts: &TS, sc: &Scope, s: Option<&'a Sentence>) -> bool {
        let _ = (sc, s);
        let mut i = ts.pos;
        let is_lit = |t: &Token| matches!(t, Token::Whole { .. } | Token::Decimal { .. });
        if !ts.toks.get(i).map(is_lit).unwrap_or(false) {
            return false;
        }
        let mut seen_two = false;
        loop {
            i += 1;
            match ts.toks.get(i) {
                Some(Token::Word { lower, .. }) if lower == "and" => {}
                Some(Token::Word { lower, .. })
                    if matches!(lower.as_str(), "sorted" | "reversed" | "unique") =>
                {
                    return seen_two;
                }
                _ => return false,
            }
            let lit = ts.toks.get(i + 1).map(is_lit).unwrap_or(false);
            if !lit {
                return false;
            }
            i += 1;
            seen_two = true;
        }
    }

    /// Parse the literal run started by try_and_list_head: lit (and lit)+.
    fn and_list_operand(&self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        let _ = (sc, s);
        let mut items: Vec<Expr> = Vec::new();
        let is_lit = |t: &Token| matches!(t, Token::Whole { .. } | Token::Decimal { .. });
        loop {
            match ts.peek() {
                Some(t) if is_lit(t) => match t {
                    Token::Whole { value } => {
                        items.push(Expr {
                            kind: Kind::Whole,
                            e: E::Whole(*value),
                            dis: value.to_string(),
                            can_fail: false,
                            num_word: false,
                        });
                        ts.pos += 1;
                    }
                    Token::Decimal { value } => {
                        items.push(Expr {
                            kind: Kind::Decimal,
                            e: E::Dec(*value),
                            dis: lit_dec(*value),
                            can_fail: false,
                            num_word: false,
                        });
                        ts.pos += 1;
                    }
                    _ => unreachable!(),
                },
                _ => break,
            }
            if ts.peek_word() == Some("and") {
                ts.pos += 1;
            } else {
                break;
            }
        }
        let k = items
            .first()
            .map(|e| e.kind.clone())
            .unwrap_or(Kind::Unknown);
        Expr {
            kind: Kind::List(Box::new(k)),
            e: E::ListOf(items),
            dis: "list".to_string(),
            can_fail: false,
            num_word: false,
        }
    }

    /// An operand of a math word: never a text value (Ch.4, rule 3).
    fn op_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        let saved = self.text_depth;
        self.text_depth = 0;
        let e = self.parse_operand(ts, sc, s);
        self.text_depth = saved;
        e
    }

    /// A function-call input is a value position: an unknown word is text
    /// (Ch.4 rule 2; Ch.15 greet Maya.).
    fn arg_operand(&mut self, ts: &mut TS, sc: &Scope, s: Option<&'a Sentence>) -> Expr {
        self.text_depth += 1;
        let e = self.parse_operand(ts, sc, s);
        self.text_depth -= 1;
        e
    }

    fn plain_word_operand(
        &mut self,
        ts: &mut TS,
        text: &str,
        lower: &str,
        sc: &Scope,
        s: Option<&'a Sentence>,
    ) -> Expr {
        // M4-10 (G77/S68): the reads of request inside a handler body
        // (method/page/text/data/header NAME/query NAME/parameter NAME
        // of request); checked before the record-part speculation,
        // because request is not a declared record.
        if self.in_handler > 0 {
            if let Some(e) = self.try_request_read(ts, lower) {
                return e;
            }
        }
        // "name of maya" reads a record part (ch.20); speculate on "of"
        // (a Some leaves the cursor after the base record already)
        if ts.peek_next() == Some("of") {
            if let Some(e) = self.spec_part_of(ts, lower, sc, s) {
                return e;
            }
        }
        // a pattern word outside replace / position of / split is T0153 (ch.14)
        if is_pattern_only_word(lower) {
            if let Some(ss) = s {
                self.err(
                    "T0153",
                    format!(
                        "{lower} is a pattern word used outside replace, position of or split."
                    ),
                    ss,
                    0,
                    ss.text.len(),
                    "digits, letters, optional and the like are used outside a text pattern."
                        .to_string(),
                    "Use them only in replace, position of or split.".to_string(),
                );
            }
            ts.pos += 1;
            return Expr {
                kind: Kind::Text,
                e: E::Word(text.to_string()),
                dis: text.to_string(),
                can_fail: false,
                num_word: false,
            };
        }
        // a spelled number word is text unless converted with as text
        if is_number_word(lower) {
            ts.pos += 1;
            let mut e = Expr {
                kind: Kind::Text,
                e: E::Word(text.to_string()),
                dis: text.to_string(),
                can_fail: false,
                num_word: true,
            };
            if ts.peek_word() == Some("as") {
                let save = ts.pos;
                ts.pos += 1;
                if ts.peek_word() == Some("text") {
                    ts.pos += 1;
                    e.num_word = false; // "five as text" is the approved text value
                } else {
                    ts.pos = save;
                }
            }
            return e;
        }
        // multiword defined name at the cursor?
        if let Some(n) = self.match_name_at(ts, text) {
            self.check_ambiguous_name(ts, &n, s);
            let lower = n.to_ascii_lowercase();
            let found = sc.find(&lower);
            if found.is_none() {
                if let Some(ss) = s {
                    let (lo, hi) = span_of(&ss.text, &n);
                    if self.fn_outer_changeables.iter().any(|x| x == &lower) {
                        if self.in_live > 0 {
                            // M4-S73/D13 (Route A): a live session runs
                            // against the server frame itself, so it
                            // reads and writes the program's own
                            // top-level Changeable names (the shared
                            // connection list is the broadcast
                            // mechanism). The sessions are resumable
                            // blocks run one pass at a time on the
                            // accept loop: there is no concurrent task
                            // here to race, so the T0451 capture
                            // prohibition does not apply.
                        } else if self.in_task > 0 {
                            // T0451: a task captures only fixed names
                            // (M4-S2); a Changeable cannot cross into a
                            // task body.
                            self.err(
                                "T0451",
                                format!("{lower} is a Changeable name from outside."),
                                ss,
                                lo,
                                hi,
                                "Task captures a Changeable name.".to_string(),
                                "Pass it as an input, or capture a fixed name.".to_string(),
                            );
                        } else {
                            // T0204: a function does not see an outer Changeable (ch.66)
                            self.err(
                                "T0204",
                                format!("{lower} is a Changeable name from outside the function."),
                                ss,
                                lo,
                                hi,
                                "A function uses a Changeable name from outside.".to_string(),
                                "Pass it as an input.".to_string(),
                            );
                        }
                    } else if let Some(m) = crate::unshared_module_of(&lower) {
                        self.err(
                            "T0208",
                            format!(
                                "{lower} is not shared by {m}. Add Share {lower}. to {m}.lykaon."
                            ),
                            ss,
                            lo,
                            hi,
                            format!("{lower} belongs to module {m}, which does not share it."),
                            format!("Add Share {lower}. to {m}.lykaon, or use a shared name."),
                        );
                    } else if !(sc.find_task(&lower)
                        && s.is_some_and(|ss| task_escape_shape(&ss.text, &lower)))
                    {
                        self.err(
                            "T0205",
                            format!("{n} is not defined."),
                            ss,
                            lo,
                            hi,
                            format!("{n} is used where it is not defined."),
                            "Define it first, or check the spelling.".to_string(),
                        );
                    }
                }
            }
            let kind = found.map(|d| d.kind).unwrap_or(Kind::Unknown);
            return Expr {
                kind,
                e: E::Name(lower),
                dis: n,
                can_fail: false,
                num_word: false,
            };
        }
        // function call: name arg [with arg]*
        if self.is_function_name(lower) {
            let name = lower.to_string();
            ts.pos += 1;
            let mut args = Vec::new();
            let next_is_arg = match ts.peek() {
                None | Some(Token::Period) | Some(Token::Eof) => false,
                Some(Token::Word { lower, .. }) => {
                    // "minus 2" after a call name is a negative literal arg;
                    // "minus n" is the negation of the variable
                    if lower == "minus" {
                        matches!(
                            ts.toks.get(ts.pos + 1),
                            Some(Token::Whole { .. }) | Some(Token::Decimal { .. })
                        ) || matches!(
                            ts.toks.get(ts.pos + 1),
                            Some(Token::Word { lower: w, .. }) if !is_op_word(w)
                        )
                    } else {
                        !is_op_word(lower)
                    }
                }
                _ => true,
            };
            if next_is_arg {
                args.push(self.arg_operand(ts, sc, s));
            }
            while ts.peek_word() == Some("with") {
                ts.pos += 1;
                args.push(self.arg_operand(ts, sc, s));
            }
            self.check_arity(&name, args.len(), &arg_kinds_of(&args), s);
            let call_can_fail = self.func_can_fail(&name);
            return Expr {
                kind: Kind::Unknown,
                e: E::Call { name, args },
                dis: text.to_string(),
                can_fail: call_can_fail,
                num_word: false,
            };
        }
        // a defined single-word name ...else an undefined word: text in a
        // value position (Ch.4, rule 2), an error in a math-operand position
        // (Ch.4, rule 3).
        ts.pos += 1;
        let found = sc.find(lower);
        if found.is_none() {
            if self.text_depth > 0 {
                return Expr {
                    kind: Kind::Text,
                    e: E::Word(text.to_string()),
                    dis: text.to_string(),
                    can_fail: false,
                    num_word: false,
                };
            }
            // a text word just before a postfix word is a value position
            // (G73: postfix follows "a name, a number, a text word or a list of items")
            if ts
                .peek_word()
                .map(|w| {
                    matches!(
                        w,
                        "sorted"
                            | "reversed"
                            | "unique"
                            | "trimmed"
                            | "backwards"
                            | "normalized"
                            | "fallback"
                    )
                })
                .unwrap_or(false)
            {
                return Expr {
                    kind: Kind::Text,
                    e: E::Word(text.to_string()),
                    dis: text.to_string(),
                    can_fail: false,
                    num_word: false,
                };
            }
            if let Some(ss) = s {
                let (lo, hi) = span_of(&ss.text, text);
                if let Some(m) = crate::unshared_module_of(lower) {
                    self.err(
                        "T0208",
                        format!("{lower} is not shared by {m}. Add Share {lower}. to {m}.lykaon."),
                        ss,
                        lo,
                        hi,
                        format!("{lower} belongs to module {m}, which does not share it."),
                        format!("Add Share {lower}. to {m}.lykaon, or use a shared name."),
                    );
                } else if !(sc.find_task(&lower)
                    && s.is_some_and(|ss| task_escape_shape(&ss.text, &lower)))
                {
                    self.err(
                        "T0205",
                        format!("{text} is not defined."),
                        ss,
                        lo,
                        hi,
                        format!("{text} is used where it is not defined."),
                        "Define it first, or check the spelling.".to_string(),
                    );
                }
            }
        }
        let kind = found.map(|d| d.kind).unwrap_or(Kind::Unknown);
        Expr {
            kind,
            e: E::Name(lower.to_string()),
            dis: text.to_string(),
            can_fail: false,
            num_word: false,
        }
    }

    fn is_function_name(&self, w: &str) -> bool {
        self.func_names.iter().any(|f| f == w)
    }
    /// Whether a declared function is marked can fail (ch.19).
    fn func_can_fail(&self, name: &str) -> bool {
        self.funcs.iter().any(|f| f.name == name && f.can_fail)
    }

    // ------------------------------------------------------------ helpers

    /// Match the longest defined name starting at the cursor; consume it.
    /// T0120 (ch.4): when the longest name (k words) matches at the
    /// cursor and a DIFFERENT name of the same length k matches one word
    /// later, the run has two readings (`Say red car seat.` with Red car
    /// and Car seat). Ambiguity is found while reading, before any later
    /// check (ch.66), and the compiler never chooses (ch.65).
    fn check_ambiguous_name(&mut self, ts: &TS, matched: &str, s: Option<&'a Sentence>) {
        let k = matched.split_whitespace().count();
        if k < 2 {
            return; // one word cannot overlap itself
        }
        // the match just ended at ts.pos; the other name starts one
        // word into the matched name
        let end = ts.pos;
        let start2 = end - k + 1;
        let mut words2: Vec<&str> = Vec::new();
        let mut p = start2;
        while p < ts.toks.len() && words2.len() < k {
            match &ts.toks[p] {
                Token::Word { text, .. } => {
                    words2.push(text.as_str());
                    p += 1;
                }
                _ => break,
            }
        }
        if words2.len() != k {
            return;
        }
        let mut other: Option<String> = None;
        for cand in &self.names {
            let parts: Vec<&str> = cand.split_whitespace().collect();
            if parts.len() == k
                && parts
                    .iter()
                    .enumerate()
                    .all(|(i, x)| words2[i].eq_ignore_ascii_case(x))
            {
                other = Some(parts.join(" "));
                break;
            }
        }
        let Some(other) = other else { return };
        if other.eq_ignore_ascii_case(matched) {
            return; // the same spelling twice is not two different names
        }
        let Some(ss) = s else { return };
        // the whole run: the matched name plus the overlapping one
        let run_start = end - k;
        let mut run: Vec<&str> = Vec::new();
        let mut p = run_start;
        while p < ts.toks.len() && run.len() < k + 1 {
            match &ts.toks[p] {
                Token::Word { text, .. } => {
                    run.push(text.as_str());
                    p += 1;
                }
                _ => break,
            }
        }
        let run_text = run.join(" ");
        let (lo, hi) = span_of(&ss.text, &run_text);
        self.err(
            "T0120",
            format!("{run_text} can mean {matched} or {other}."),
            ss,
            lo,
            hi,
            "Two different names of the same length fit the words.".to_string(),
            "Rename one of them.".to_string(),
        );
    }

    fn match_name_at(&mut self, ts: &mut TS, first: &str) -> Option<String> {
        let save = ts.pos;
        let mut words: Vec<String> = Vec::new();
        let mut p = ts.pos;
        while p < ts.toks.len() && words.len() <= 4 {
            match &ts.toks[p] {
                Token::Word { text, .. } => {
                    words.push(text.clone());
                    p += 1;
                }
                _ => break,
            }
        }
        // the name being defined is not in scope until its sentence ends (ch.20)
        if let Some(d) = &self.defining {
            if words.len() == d.split_whitespace().count()
                && words
                    .iter()
                    .zip(d.split_whitespace())
                    .all(|(w, x)| w.eq_ignore_ascii_case(x))
            {
                return None;
            }
        }
        for n in &self.names {
            let parts: Vec<&str> = n.split_whitespace().collect();
            if parts.is_empty() || !parts[0].eq_ignore_ascii_case(first) {
                continue;
            }
            if parts.len() > words.len() {
                continue;
            }
            if parts
                .iter()
                .enumerate()
                .all(|(i, x)| words[i].eq_ignore_ascii_case(x))
            {
                ts.pos = save + parts.len();
                return Some(parts.join(" "));
            }
        }
        ts.pos = save;
        None
    }

    /// Longest name match for a Set target.
    fn match_name(&mut self, ts: &mut TS) -> Option<String> {
        let w = ts.peek_word()?.to_string();
        if let Some(n) = self.match_name_at(ts, &w) {
            return Some(n.to_ascii_lowercase());
        }
        ts.pos += 1;
        Some(w.to_ascii_lowercase())
    }
}

// ---------------------------------------------------------------- helpers

fn lit_whole(v: i64) -> Expr {
    Expr {
        kind: Kind::Whole,
        e: E::Whole(v),
        dis: v.to_string(),
        can_fail: false,
        num_word: false,
    }
}

fn lit_dec(v: f64) -> String {
    format!("{v:?}")
}

fn flat_empty() -> Expr {
    Expr {
        kind: Kind::Text,
        e: E::Flat(Vec::new()),
        dis: String::new(),
        can_fail: false,
        num_word: false,
    }
}

fn unknown_it() -> Expr {
    Expr {
        kind: Kind::Unknown,
        e: E::It,
        dis: String::new(),
        can_fail: false,
        num_word: false,
    }
}

fn boolean_cmp(c: Comp) -> Expr {
    Expr {
        kind: Kind::Boolean,
        e: E::Compare(c),
        dis: String::new(),
        can_fail: false,
        num_word: false,
    }
}

/// and/or chains evaluate both sides (the syntax layer rejects mixing them).
fn make_and_or(l: Expr, r: Expr, is_and: bool) -> Expr {
    Expr {
        kind: Kind::Boolean,
        e: E::AndOr(Box::new(l), Box::new(r), is_and),
        dis: String::new(),
        can_fail: false,
        num_word: false,
    }
}

/// Raw words for Say literally.
fn flat_words(toks: &[Token]) -> Expr {
    let parts: Vec<Expr> = toks
        .iter()
        .filter(|t| !matches!(t, Token::Eof | Token::Period))
        .map(|t| match t {
            Token::Word { text, .. } => Expr {
                kind: Kind::Text,
                e: E::Word(text.clone()),
                dis: String::new(),
                can_fail: false,
                num_word: false,
            },
            Token::Whole { value } => Expr {
                kind: Kind::Whole,
                e: E::Whole(*value),
                dis: value.to_string(),
                can_fail: false,
                num_word: false,
            },
            Token::Decimal { value } => Expr {
                kind: Kind::Decimal,
                e: E::Dec(*value),
                dis: lit_dec(*value),
                can_fail: false,
                num_word: false,
            },
            Token::YesNo { value } => Expr {
                kind: Kind::Boolean,
                e: E::Boolean(*value),
                dis: String::new(),
                can_fail: false,
                num_word: false,
            },
            Token::Negative { value } => Expr {
                kind: Kind::Whole,
                e: E::Whole(-*value),
                dis: format!("minus {value}"),
                can_fail: false,
                num_word: false,
            },
            _ => Expr {
                kind: Kind::Text,
                e: E::Word(String::new()),
                dis: String::new(),
                can_fail: false,
                num_word: false,
            },
        })
        .collect();
    Expr {
        kind: Kind::Text,
        e: E::Flat(parts),
        dis: String::new(),
        can_fail: false,
        num_word: false,
    }
}

fn toks_of(text: &str) -> Vec<Token> {
    Lexer::new(text).tokenize().0
}

/// The lowercase word of a Word token, boxed to own it.
fn w_lower_tok(t: &Token) -> Option<String> {
    match t {
        Token::Word { lower, .. } => Some(lower.clone()),
        _ => None,
    }
}

fn first_word_lower(text: &str) -> String {
    text.split_whitespace()
        .next()
        .unwrap_or("")
        .trim_end_matches('.')
        .to_ascii_lowercase()
}

/// A function whose body contains Hand back is a generator (M3-S30).
pub fn body_has_hand_back(b: &FnBody) -> bool {
    fn stmts(s: &[Stmt]) -> bool {
        s.iter().any(|st| match st {
            Stmt::HandBack(_) => true,
            Stmt::If { branches, other } => {
                branches.iter().any(|(_, b)| stmts(b)) || other.as_ref().map_or(false, |o| stmts(o))
            }
            Stmt::RepeatTimes { body, .. } | Stmt::RepeatForever { body } => stmts(body),
            Stmt::RepeatWhile { body, .. }
            | Stmt::ForRange { body, .. }
            | Stmt::ForIn { body, .. } => stmts(body),
            Stmt::Try {
                success, failure, ..
            } => stmts(success) || failure.iter().any(|(_, b)| stmts(b)),
            _ => false,
        })
    }
    match b {
        FnBody::Block(ss) => stmts(ss),
        _ => false,
    }
}

fn is_number_word(w: &str) -> bool {
    matches!(
        w.to_ascii_lowercase().as_str(),
        "zero"
            | "one"
            | "two"
            | "three"
            | "four"
            | "five"
            | "six"
            | "seven"
            | "eight"
            | "nine"
            | "ten"
            | "eleven"
            | "twelve"
            | "thirteen"
            | "fourteen"
            | "fifteen"
            | "sixteen"
            | "seventeen"
            | "eighteen"
            | "nineteen"
            | "twenty"
            | "thirty"
            | "forty"
            | "fifty"
            | "sixty"
            | "seventy"
            | "eighty"
            | "ninety"
            | "hundred"
            | "thousand"
            | "million"
    )
}

fn is_op_word(w: &str) -> bool {
    matches!(
        w,
        "plus" | "minus" | "times" | "divided" | "whole" | "rounded" | "factorial" | "as"
    )
}

/// Words that carry their own "X of ..." structure and must never be read as
/// record parts (ch.20 part reads "name of maya" only apply to plain words).
const OF_STRUCTURE_WORDS: &[&str] = &[
    "item",
    "first",
    "second",
    "last",
    "position",
    "value",
    "how",
    "lower",
    "upper",
    "joined",
    "union",
    "overlap",
    "difference",
    "list",
    "pair",
    "safe",
    "copy",
];

/// The lowercase word of a Word token.
fn w_lower(t: &Token) -> Option<&String> {
    match t {
        Token::Word { lower, .. } => Some(lower),
        _ => None,
    }
}

fn has_operation_word(toks: &[Token]) -> bool {
    toks.iter().any(|t| match t {
        Token::Word { lower, .. } => matches!(
            lower.as_str(),
            "plus" | "minus" | "times" | "divided" | "remainder" | "power" | "rounded"
                | "factorial" | "how" | "lower" | "as" | "list" | "pair" | "first" | "second"
                | "joined" | "sorted" | "item" | "last" | "position" | "value" | "safe"
                | "union" | "overlap" | "difference" | "split" | "replace"
                | "items" | "fallback" | "reversed" | "unique"
                | "upper" | "trimmed" | "backwards" | "normalized"
                // M3 value forms (ch.24-25): <list> where <cond>,
                // first N fibonacci, primes to N.
                | "where" | "primes" | "fibonacci"
        ),
        _ => false,
    })
}

/// M4-7 (Appendix K G6): a time unit word, in the spellings the
/// grammar lists (the singular forms are a logged parser cut).
fn m4_time_unit(w: &str) -> Option<&'static str> {
    match w {
        "milliseconds" => Some("milliseconds"),
        "seconds" => Some("seconds"),
        "minutes" => Some("minutes"),
        "hours" => Some("hours"),
        "days" => Some("days"),
        "weeks" => Some("weeks"),
        _ => None,
    }
}

/// The length of one time unit in nanoseconds (M4-S52: nanosecond
/// precision; months and years are not units in M4).
fn m4_unit_nanos(unit: &str) -> i128 {
    match unit {
        "milliseconds" => 1_000_000,
        "seconds" => 1_000_000_000,
        "minutes" => 60_000_000_000,
        "hours" => 3_600_000_000_000,
        "days" => 86_400_000_000_000,
        "weeks" => 604_800_000_000_000,
        _ => 0,
    }
}

/// Does a text pattern start with this word? (ch.14, M2-G31)
fn pattern_word_starts(w: &str) -> bool {
    matches!(
        w,
        "digits" | "letters" | "spaces" | "anything" | "one" | "optional" | "starts" | "ends"
    )
}

/// A word that only belongs inside a text pattern (T0153 when seen elsewhere).
fn is_pattern_only_word(w: &str) -> bool {
    matches!(w, "digits" | "letters" | "spaces" | "anything")
}

fn is_num_kind(k: &Kind) -> bool {
    matches!(k, Kind::Whole | Kind::Decimal | Kind::Big)
}

/// A maybe-kind operand meeting a math operation is T0310 (ch.18).
fn maybe_warn(maybe: &Expr, other: &Expr) -> bool {
    matches!(maybe.kind, Kind::Maybe(ref inner) if **inner != Kind::Unknown)
        && (is_num_kind(&other.kind) || other.kind == Kind::Unknown)
}

fn num_kind(a: &Kind, b: &Kind) -> Kind {
    if (is_num_kind(a) || a == &Kind::Unknown) && (is_num_kind(b) || b == &Kind::Unknown) {
        if a == &Kind::Decimal || b == &Kind::Decimal {
            Kind::Decimal
        } else if a == &Kind::Big || b == &Kind::Big {
            Kind::Big
        } else {
            Kind::Whole
        }
    } else {
        a.clone()
    }
}

/// Byte span of a name sequence inside a sentence, for Where marks.
fn span_of(text: &str, name: &str) -> (usize, usize) {
    let lower_text = text.to_ascii_lowercase();
    let want: Vec<&str> = name.split_whitespace().collect();
    if want.is_empty() {
        return (0, 0);
    }
    let mut byte = 0usize;
    let mut start = None;
    let mut end = 0usize;
    let mut count = 0usize;
    for w in lower_text.split(' ') {
        let wlen = w.len();
        let wstart = byte;
        byte += wlen + 1;
        if start.is_none() {
            if w == want[0] {
                start = Some(wstart);
                count = 1;
                end = wstart + wlen;
            }
        } else {
            let expected = want.get(count).copied().unwrap_or("\u{0}");
            if w.eq_ignore_ascii_case(expected) && count < want.len() {
                count += 1;
                end = wstart + wlen;
            } else {
                break;
            }
        }
    }
    match start {
        Some(st) => (st, end.max(st + 1)),
        None => {
            // fallback: first word
            let first = text.split_whitespace().next().unwrap_or("").len();
            (0, first)
        }
    }
}

/// Shapes that keep a task handle past its block (T0462): `Give back <name>`,
/// `Add <name> to <collection>.` and `Set <other> to <name>.`. T0462 reports
/// them; the name is a task, not a value, so the undefined-name error must not
/// pile on for the same sentence.
fn task_escape_shape(text: &str, name: &str) -> bool {
    let lowered = text.to_ascii_lowercase();
    let words: Vec<&str> = lowered
        .split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .filter(|w| !w.is_empty())
        .collect();
    let is_name = |w: &str| w.eq_ignore_ascii_case(name);
    let returned =
        words.len() >= 3 && words[0] == "give" && words[1] == "back" && is_name(words[2]);
    let stored = words.len() >= 3 && words[0] == "add" && is_name(words[1]) && words[2] == "to";
    let assigned = words.first() == Some(&"set")
        && words
            .iter()
            .position(|w| is_name(w))
            .is_some_and(|pos| pos > 0 && words[pos - 1] == "to");
    returned || stored || assigned
}

/// Does a value of kind `given` belong in a place declared as `declared`?
/// The checker only rejects what it can see: an unknown or missing kind is
/// never an error, the three number kinds are interchangeable (the language's
/// `number` wall accepts a whole or a decimal), and the collection kinds
/// compare their element kinds. Everything else must match exactly.
fn kind_fits(declared: &Kind, given: &Kind) -> bool {
    match (declared, given) {
        (Kind::Unknown, _) | (_, Kind::Unknown) | (_, Kind::Missing) => true,
        (Kind::Whole | Kind::Decimal | Kind::Big, Kind::Whole | Kind::Decimal | Kind::Big) => true,
        (Kind::List(a), Kind::List(b))
        | (Kind::Maybe(a), Kind::Maybe(b))
        | (Kind::Set(a), Kind::Set(b))
        | (Kind::Queue(a), Kind::Queue(b))
        | (Kind::Array(a), Kind::Array(b))
        | (Kind::Channel(a), Kind::Channel(b))
        | (Kind::Guarded(a), Kind::Guarded(b))
        | (Kind::Secret(a), Kind::Secret(b)) => kind_fits(a, b),
        (Kind::Map(ka, va), Kind::Map(kb, vb)) => kind_fits(ka, kb) && kind_fits(va, vb),
        (Kind::Pair(a1, b1), Kind::Pair(a2, b2)) => kind_fits(a1, a2) && kind_fits(b1, b2),
        _ => declared == given,
    }
}

/// Byte span of one name at a word boundary. `span_of` splits on spaces, so a
/// name at the end of the sentence (`Say items.`) never matches; this one also
/// ignores the sentence's punctuation.
fn name_span(text: &str, name: &str) -> (usize, usize) {
    let lower = text.to_ascii_lowercase();
    let bytes = lower.as_bytes();
    let want = name.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    if !want.is_empty() {
        let mut i = 0usize;
        'try_start: while i + want.len() <= bytes.len() {
            for (k, &b) in want.iter().enumerate() {
                if bytes[i + k] != b {
                    i += 1;
                    continue 'try_start;
                }
            }
            let starts_ok = i == 0 || !is_word(bytes[i - 1]);
            let end = i + want.len();
            let ends_ok = end == bytes.len() || !is_word(bytes[end]);
            if starts_ok && ends_ok {
                return (i, end);
            }
            i += 1;
        }
    }
    span_of(text, name)
}

/// Sentences of a later milestone fail with T0509 (Appendix O). The coarse
/// shapes cover the deferred book examples (lists are Chapter 11 = M2).
pub(crate) fn later_milestone_shape(text: &str) -> Option<String> {
    // the sentence's own period is not part of the shape: `Run safely.`
    // must match the `run safely` phrase exactly like `Run safely` would
    let t = text.trim().trim_end_matches('.').to_ascii_lowercase();
    let words: Vec<&str> = t.split_whitespace().collect();
    // Sorted / first-2-of and friends are M2 list operations, but the ch.65
    // ambiguity example must first give T0130, so no T0509 here for that shape.
    for w in words.windows(2) {
        if w[0] == "lend" && w[1] == "to" && words.windows(3).any(|x| x[2] == "change") {
            // "To pad lend to change items." (Ch.76) is an M1b example; the
            // interpreter gives the function its own copy, like M2's check
            // would do for out-call semantics.
            return None;
        }
    }
    // Appendix K 1.1: databases, Load, Plot, Predict, the sandbox, Limit
    // memory/time, encryption, screens and bridges are NOT in M4; a later
    // sentence gives T0509 and never crashes the compiler. The phrases
    // (not just the first word) keep ordinary names such as `load` usable.
    const LATER: [&str; 22] = [
        "limit memory",
        "limit time",
        "load the",
        "load a model",
        "load data",
        "plot ",
        "plot",
        "predict ",
        "predict",
        "open database",
        "open the database",
        "query the database",
        "sqlite",
        "encrypt ",
        "decrypt ",
        "show screen",
        "screen ",
        "bridge ",
        "run safely",
        "train the model",
        "gpu ",
        "compile to wasm",
    ];
    for phrase in LATER {
        let p = phrase.trim_end();
        if t == p || t.starts_with(&format!("{p} ")) {
            return Some(
                "A sentence belongs to a later milestone and is not yet implemented.".to_string(),
            );
        }
    }
    None
}

/// A Say whose entire content is just `it` or `them` (Ch.16 compile check).
fn pure_pronoun(st: &Stmt) -> Option<&'static str> {
    match st {
        Stmt::Say { expr, .. } => match &expr.e {
            E::Flat(pieces) if pieces.len() == 1 => match &pieces[0].e {
                E::It => Some("it"),
                E::Them => Some("them"),
                _ => None,
            },
            E::It => Some("it"),
            E::Them => Some("them"),
            _ => None,
        },
        _ => None,
    }
}

/// The kinds of a call's argument expressions (T0316's check).
fn arg_kinds_of(args: &[Expr]) -> Vec<Kind> {
    args.iter().map(|a| a.kind.clone()).collect()
}

/// The text a Say would print, when every piece is a plain word (used by the
/// T0220 message: "the sentence before printed hello").
fn static_say_text(expr: &Expr) -> String {
    match &expr.e {
        E::Flat(pieces) => {
            let mut parts = Vec::new();
            for p in pieces {
                if let E::Word(t) = &p.e {
                    parts.push(t.clone());
                } else {
                    return String::new();
                }
            }
            parts.join(" ")
        }
        // a one-word run was collapsed into its single word
        E::Word(t) => t.clone(),
        _ => String::new(),
    }
}

fn stmt_can_fail(st: &Stmt) -> bool {
    match st {
        Stmt::Define(d) => expr_can_fail(&d.expr),
        Stmt::Ask { kind, .. } => !matches!(kind, AskKind::Text),
        Stmt::Evaluate { expr, .. } => expr_can_fail(expr),
        Stmt::Close { .. } => true,
        // M4-S24 (Appendix K): a failure inside a Spread stops the other
        // workers and is the failure of the Spread sentence - the sentence
        // is can fail when its items value or any sentence in its body can.
        Stmt::Spread { items, body } => expr_can_fail(items) || any_can_fail(body),
        _ => false,
    }
}

/// Can any sentence of this block produce a failure that could propagate?
/// Walks nested blocks too; a Try sentence's own failure is handled by the
/// Try, but its success and If that fails bodies must stand on their own.
fn any_can_fail(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::If { branches, other } => {
            branches.iter().any(|(_, ss)| any_can_fail(ss))
                || other.iter().any(|ss| any_can_fail(ss))
        }
        Stmt::RepeatTimes { body, .. }
        | Stmt::RepeatWhile { body, .. }
        | Stmt::RepeatForever { body }
        | Stmt::ForRange { body, .. }
        | Stmt::ForIn { body, .. }
        | Stmt::StartTask { body, .. }
        | Stmt::DoTogether { body }
        | Stmt::AfterTimer { body, .. }
        | Stmt::EveryTimer { body, .. }
        | Stmt::StreamLoop { body, .. }
        | Stmt::Check { body, .. }
        | Stmt::Test { body, .. } => any_can_fail(body),
        Stmt::Try {
            sentence,
            success,
            failure,
        } => {
            stmt_can_fail(sentence)
                || any_can_fail(success)
                || failure.iter().any(|(_, ss)| any_can_fail(ss))
        }
        other => stmt_can_fail(other),
    })
}

fn expr_can_fail(e: &Expr) -> bool {
    if e.can_fail {
        return true;
    }
    match &e.e {
        E::AsNumber(inner) => {
            expr_can_fail(inner) || inner.kind == Kind::Text || inner.kind == Kind::Unknown
        }
        E::Neg(x)
        | E::Round(x, _)
        | E::Factorial(x)
        | E::CountIn(x)
        | E::Lower(x)
        | E::AsWhole(x)
        | E::AsDecimal(x)
        | E::AsText(x) => expr_can_fail(x),
        E::Move(inner) | E::Share(inner) | E::CopyOf(inner) | E::WeakShare(inner) => {
            expr_can_fail(inner)
        }
        E::Binary { l, r, .. } | E::DivWhole(l, r) | E::Rem(l, r) | E::Pow(l, r) => {
            expr_can_fail(l) || expr_can_fail(r)
        }
        _ => false,
    }
}

fn with_fallback(st: Stmt, fb: Expr) -> Stmt {
    match st {
        Stmt::Define(mut d) => {
            d.fallback = Some(fb);
            Stmt::Define(d)
        }
        Stmt::Ask { name, kind, .. } => Stmt::Ask {
            name,
            kind,
            fallback: Some(fb),
        },
        other => other,
    }
}

// ---------------------------------------------------------------- ownership (ch.28-31)

/// Kind for a property-test generator phrase (ch.38).
fn prop_kind(words: &str) -> Kind {
    match words {
        "number" | "whole" => Kind::Whole,
        "decimal" => Kind::Decimal,
        "text" => Kind::Text,
        "truth" => Kind::Boolean,
        "letter" => Kind::Letter,
        "list of numbers" => Kind::List(Box::new(Kind::Whole)),
        "list of texts" => Kind::List(Box::new(Kind::Text)),
        other => {
            if let Some(rest) = other.strip_prefix("list of ") {
                Kind::List(Box::new(prop_kind(rest)))
            } else if let Some(rest) = other.strip_prefix("maybe ") {
                Kind::Maybe(Box::new(prop_kind(rest)))
            } else {
                Kind::Unknown
            }
        }
    }
}

/// A move kind is moved when it is stored, given or returned; a copy kind is
/// copied and the old name stays usable (ch.28, M2-S1/M2-S2). Until M3,
/// records are always move kinds.
fn is_move_kind(kind: &Kind) -> bool {
    match kind {
        Kind::List(..)
        | Kind::Map(..)
        | Kind::Set(..)
        | Kind::Queue(..)
        | Kind::Record(..)
        | Kind::Share => true,
        Kind::Pair(a, b) => is_move_kind(a) || is_move_kind(b),
        Kind::Array(a) | Kind::Maybe(a) => is_move_kind(a),
        Kind::Enum(variants) => variants
            .iter()
            .any(|(_, parts)| parts.iter().any(|(_, k)| is_move_kind(k))),
        _ => false,
    }
}

/// The state of one name while checking ownership.
#[derive(Clone, Debug)]
struct VarState {
    kind: Kind,
    mutable: bool,
    alive: bool,
    mode: ParamMode,
}

/// The ownership environment for one block of statements (ch.28-31).
#[derive(Clone, Debug)]
struct OwnEnv {
    vars: HashMap<String, VarState>,
    /// A list held by an enclosing For each loop (shared borrow for the whole
    /// loop). Changing it inside the loop is T0402.
    foreach_read: Option<String>,
    /// Where a moved value went (ch.28): old name -> new owner, for the
    /// T0401 message.
    moved_to: HashMap<String, String>,
    /// The current function's input names (all are borrows, ch.28).
    params: Vec<String>,
}

impl OwnEnv {
    fn new() -> Self {
        OwnEnv {
            vars: HashMap::new(),
            foreach_read: None,
            moved_to: HashMap::new(),
            params: Vec::new(),
        }
    }
}

/// Kill a name that was moved away (ch.28, M2-S2). Copy kinds are never dead.
/// The sentence text with its first word removed, trimmed: "Test double works."
/// -> "double works." (ch.38 test names are raw text).
fn text_after_first_word(s: &str) -> String {
    let trimmed = s.trim();
    match trimmed.split_once(|c: char| c.is_whitespace()) {
        Some((_, rest)) => rest.trim().to_string(),
        None => String::new(),
    }
}

fn kill_name(env: &mut OwnEnv, name: &str) {
    if let Some(v) = env.vars.get_mut(name) {
        if is_move_kind(&v.kind) {
            v.alive = false;
        }
    }
}

/// The T0401 message parts (Reference 2, ch.28): What names the giver and
/// the new owner when known, Why is the catalog Cause, Fix the catalog Fix.
fn t0401_parts(env: &OwnEnv, name: &str) -> (String, String, String) {
    match env.moved_to.get(name) {
        Some(new) => (
            format!("{name} was given to {new} and can no longer be used."),
            "A name is used after its value was given away.".to_string(),
            format!("Use {new}, or write copy of {name}."),
        ),
        None => (
            format!("{name} was given away and can no longer be used."),
            "A name is used after its value was given away.".to_string(),
            "Use the new owner or copy of.".to_string(),
        ),
    }
}

/// The T0402 message parts (Reference 2, ch.29).
fn t0402_parts(name: &str) -> (String, String, String) {
    (
        format!("{name} is being read by the loop, so it cannot be changed inside it."),
        "A value is changed while a loop or borrow is reading it.".to_string(),
        format!("Loop over copy of {name}, or collect the changes and add them after the loop."),
    )
}

/// The bare name held by an expression, if any.
fn bare_name_of(expr: &Expr) -> Option<String> {
    match &expr.e {
        E::Name(n) => Some(n.clone()),
        _ => None,
    }
}

impl<'a> Builder<'a> {
    /// Check ownership and borrowing of one block of statements (ch.28-31).
    /// s is the sentence being checked, used for error spans.
    fn check_stmts(&mut self, stmts: &[Stmt], env: &mut OwnEnv, s: Option<&'a Sentence>) {
        for st in stmts {
            self.err_reported = false;
            self.check_stmt(st, env, s);
        }
    }

    fn check_stmt(&mut self, st: &Stmt, env: &mut OwnEnv, s: Option<&'a Sentence>) {
        // a lend to change borrow is live for its sentence only (ch.29): the
        // lent names are forgotten when the sentence ends
        let saved_live = std::mem::take(&mut self.lent_live);
        self.check_stmt_inner(st, env, s);
        self.lent_live = saved_live;
    }

    fn check_stmt_inner(&mut self, st: &Stmt, env: &mut OwnEnv, s: Option<&'a Sentence>) {
        match st {
            Stmt::Define(d) => {
                // the value is evaluated before the name is bound
                if let E::Move(inner) = &d.expr.e {
                    // `Others is give names.` â€” names was given to others (ch.28)
                    if let E::Name(n) = &inner.e {
                        if env.params.iter().any(|p| p == n) {
                            // T0410: the value is given away while it is still
                            // borrowed (Reference 2)
                            self.err_opt(
                                "T0410",
                                "A value is given away while it is still borrowed.".to_string(),
                                s,
                                0,
                                0,
                                format!("{n} is still borrowed here."),
                                "End the borrow first.".to_string(),
                            );
                        }
                        env.moved_to.insert(n.clone(), d.name.clone());
                    }
                }
                self.check_expr(&d.expr, env, s);
                env.vars.insert(
                    d.name.clone(),
                    VarState {
                        kind: d.expr.kind.clone(),
                        mutable: d.mutable,
                        alive: true,
                        mode: ParamMode::Lent,
                    },
                );
            }
            Stmt::Set { name, expr } => {
                if let Some(v) = env.vars.get(name) {
                    if matches!(v.kind, Kind::Share) {
                        // T0412: a shared value cannot be changed (ch.28)
                        self.err_opt(
                            "T0412",
                            "A shared value is changed.".to_string(),
                            s,
                            0,
                            0,
                            format!("{name} is shared, and shared values cannot change."),
                            "Wrap it in guarded.".to_string(),
                        );
                    }
                    if env.foreach_read.as_deref() == Some(name) {
                        let (w, wh, fx) = t0402_parts(name);
                        self.err_opt("T0402", w, s, 0, 0, wh, fx);
                    }
                }
                self.check_expr(expr, env, s);
            }
            Stmt::SetPart { path, expr } => {
                if let Some(base) = path.last() {
                    if let Some(v) = env.vars.get(base) {
                        if env.foreach_read.as_deref() == Some(base) {
                            let (w, wh, fx) = t0402_parts(base);
                            self.err_opt("T0402", w, s, 0, 0, wh, fx);
                        }
                    }
                }
                self.check_expr(expr, env, s);
            }
            Stmt::Say { expr, .. } | Stmt::Evaluate { expr, .. } => {
                self.check_expr(expr, env, s);
            }
            Stmt::Append { value, list } => {
                if let Some(v) = env.vars.get(list) {
                    if !v.mutable {
                        self.err_opt(
                            "T0406",
                            format!("{list} is fixed and cannot be changed."),
                            s,
                            0,
                            0,
                            "Set is used on a name that is not Changeable.".to_string(),
                            format!("Define it as Changeable {list} is <first value>."),
                        );
                    }
                    if !v.alive && is_move_kind(&v.kind) {
                        let (w, wh, fx) = t0401_parts(env, list);
                        self.err_opt("T0401", w, s, 0, 0, wh, fx);
                    }
                    if env.foreach_read.as_deref() == Some(list) {
                        let (w, wh, fx) = t0402_parts(list);
                        self.err_opt("T0402", w, s, 0, 0, wh, fx);
                    }
                }
                self.check_expr(value, env, s);
                if let Some(n) = bare_name_of(value) {
                    if env
                        .vars
                        .get(n.as_str())
                        .map_or(false, |v| is_move_kind(&v.kind))
                    {
                        env.moved_to.insert(n.clone(), list.clone());
                        kill_name(env, &n);
                    }
                }
            }
            Stmt::Put { map, key, value } => {
                if let Some(v) = env.vars.get(map) {
                    if !v.mutable {
                        self.err_opt(
                            "T0406",
                            format!("{map} is fixed and cannot be changed."),
                            s,
                            0,
                            0,
                            "Set is used on a name that is not Changeable.".to_string(),
                            format!("Define it as Changeable {map} is <first value>."),
                        );
                    }
                    if !v.alive && is_move_kind(&v.kind) {
                        let (w, wh, fx) = t0401_parts(env, map);
                        self.err_opt("T0401", w, s, 0, 0, wh, fx);
                    }
                    if env.foreach_read.as_deref() == Some(map) {
                        let (w, wh, fx) = t0402_parts(map);
                        self.err_opt("T0402", w, s, 0, 0, wh, fx);
                    }
                }
                self.check_expr(value, env, s);
                if let Some(k) = key {
                    self.check_expr(k, env, s);
                    if let Some(n) = bare_name_of(k) {
                        if env
                            .vars
                            .get(n.as_str())
                            .map_or(false, |v| is_move_kind(&v.kind))
                        {
                            env.moved_to.insert(n.clone(), map.clone());
                            kill_name(env, &n);
                        }
                    }
                }
                if let Some(n) = bare_name_of(value) {
                    if env
                        .vars
                        .get(n.as_str())
                        .map_or(false, |v| is_move_kind(&v.kind))
                    {
                        env.moved_to.insert(n.clone(), map.clone());
                        kill_name(env, &n);
                    }
                }
            }
            Stmt::Remove { coll, value } => {
                if let Some(v) = env.vars.get(coll) {
                    if !v.mutable {
                        self.err_opt(
                            "T0406",
                            format!("{coll} is fixed and cannot be changed."),
                            s,
                            0,
                            0,
                            "Set is used on a name that is not Changeable.".to_string(),
                            format!("Define it as Changeable {coll} is <first value>."),
                        );
                    }
                    if !v.alive && is_move_kind(&v.kind) {
                        let (w, wh, fx) = t0401_parts(env, coll);
                        self.err_opt("T0401", w, s, 0, 0, wh, fx);
                    }
                    if env.foreach_read.as_deref() == Some(coll) {
                        let (w, wh, fx) = t0402_parts(coll);
                        self.err_opt("T0402", w, s, 0, 0, wh, fx);
                    }
                }
                self.check_expr(value, env, s);
            }
            Stmt::RemoveFirst { coll } => {
                if let Some(v) = env.vars.get(coll) {
                    if !v.mutable {
                        self.err_opt(
                            "T0406",
                            format!("{coll} is fixed and cannot be changed."),
                            s,
                            0,
                            0,
                            "Set is used on a name that is not Changeable.".to_string(),
                            format!("Define it as Changeable {coll} is <first value>."),
                        );
                    }
                    if !v.alive && is_move_kind(&v.kind) {
                        let (w, wh, fx) = t0401_parts(env, coll);
                        self.err_opt("T0401", w, s, 0, 0, wh, fx);
                    }
                    if env.foreach_read.as_deref() == Some(coll) {
                        let (w, wh, fx) = t0402_parts(coll);
                        self.err_opt("T0402", w, s, 0, 0, wh, fx);
                    }
                }
            }
            Stmt::Close { name } => {
                if let Some(v) = env.vars.get(name) {
                    if is_move_kind(&v.kind) {
                        kill_name(env, name);
                    }
                }
            }
            Stmt::Share { name } => {
                self.shared_names.push(name.clone());
            }
            Stmt::Use { .. } | Stmt::Test { .. } | Stmt::Pretend { .. } => {
                self.err_reported = false;
            }
            Stmt::Check { text, cond, .. } => {
                if let Some(c) = cond {
                    self.check_expr(c, env, s);
                }
                let _ = text;
            }
            Stmt::GiveBack(v) => {
                if let Some(v) = v {
                    self.check_expr(v, env, s);
                    if let E::Name(n) = &v.e {
                        if let Some(vs) = env.vars.get(n.as_str()) {
                            if vs.mode == ParamMode::LentToChange {
                                self.err_opt(
                                    "T0409",
                                    "A function tries to give back a borrow of an input."
                                        .to_string(),
                                    s,
                                    0,
                                    0,
                                    "Give back items. as a borrow".to_string(),
                                    "Give back copy of items.".to_string(),
                                );
                            }
                        }
                    }
                }
            }
            Stmt::ForIn { vars, list, body } => {
                self.check_expr(list, env, s);
                let saved = env.foreach_read.take();
                if let E::Name(n) = &list.e {
                    env.foreach_read = Some(n.clone());
                }
                for var in vars {
                    env.vars.insert(
                        var.clone(),
                        VarState {
                            kind: Kind::Unknown,
                            mutable: false,
                            alive: true,
                            mode: ParamMode::Lent,
                        },
                    );
                }
                self.check_stmts(body, env, s);
                env.foreach_read = saved;
            }
            Stmt::RepeatTimes { body, .. }
            | Stmt::RepeatWhile { body, .. }
            | Stmt::RepeatForever { body, .. }
            | Stmt::ForRange { body, .. } => {
                self.check_stmts(body, env, s);
            }
            Stmt::If { branches, other } => {
                for (cond, _) in branches {
                    self.check_expr(cond, env, s);
                }
                let mut branch_envs: Vec<OwnEnv> = Vec::new();
                for (_, body) in branches {
                    let mut be = env.clone();
                    self.check_stmts(body, &mut be, s);
                    branch_envs.push(be);
                }
                if let Some(ob) = other {
                    let mut be = env.clone();
                    self.check_stmts(ob, &mut be, s);
                    branch_envs.push(be);
                }
                // join: a name survives only if it is alive in every branch
                let mut joined: HashMap<String, VarState> = HashMap::new();
                for (name, v) in &env.vars {
                    let alive_all = branch_envs
                        .iter()
                        .all(|be| be.vars.get(name).map_or(false, |v2| v2.alive));
                    joined.insert(
                        name.clone(),
                        VarState {
                            alive: alive_all,
                            ..v.clone()
                        },
                    );
                }
                env.vars = joined;
            }
            Stmt::Try {
                sentence,
                success,
                failure,
            } => {
                self.check_stmt(sentence, env, s);
                self.check_stmts(success, env, s);
                for (_, body) in failure {
                    self.check_stmts(body, env, s);
                }
            }
            Stmt::Note
            | Stmt::Stop
            | Stmt::Skip
            | Stmt::Ask { .. }
            | Stmt::Fail { .. }
            | Stmt::PassFailureUp
            | Stmt::LookAt { .. }
            | Stmt::DefineEnum { .. }
            | Stmt::HandBack(_) => {}
            Stmt::DefineLocalFn(_) => {}
            // M4 (Appendix K) task sentences: the ownership checker walks
            // the task/together bodies so a moved name cannot cross into a
            // task silently; wait/sleep/stop touch nothing.
            Stmt::StartTask { body, .. } | Stmt::DoTogether { body } => {
                self.check_stmts(body, env, s);
            }
            Stmt::WaitFor { .. } | Stmt::StopTask { .. } | Stmt::SleepFor { .. } => {}
            // M4 (Appendix K): channel/guarded/atomic sentences. In this
            // first cut a Send copies the value into the channel (logged
            // deviation), so nothing is moved away; Receive/Add touch only
            // shared cells the ownership model does not track.
            Stmt::Send { value, .. } | Stmt::AtomicAdd { value, .. } => {
                self.check_expr(value, env, s);
            }
            Stmt::Receive { .. } => {}
            // M4-4 (Appendix K 7.3/7.4): the timer, stream and spread
            // sentences: their bodies are walked like a task's, a stream
            // round may rebind nothing (the loop variable is defined fresh)
            // and a spread rounds' items value is checked. Use N workers.
            // touches nothing.
            Stmt::AfterTimer { body, .. }
            | Stmt::EveryTimer { body, .. }
            | Stmt::StreamLoop { body, .. } => {
                self.check_stmts(body, env, s);
            }
            Stmt::UseWorkers { .. } => {}
            // M4-7 (7.7): Use seed touches no value.
            Stmt::UseSeed { .. } => {}
            // M4-8 (7.10/7.11): the Run arguments are checked like a
            // Send's; the signal and input loop bodies walk like a task's;
            // Exit carries only a literal code.
            Stmt::RunProc { args, .. } => {
                for a in args {
                    self.check_expr(a, env, s);
                }
            }
            Stmt::Exit { .. } => {}
            // M4-9 (7.12): the Log text is checked as in Say; Use log
            // level carries no expression.
            Stmt::Log { expr, .. } => {
                self.check_expr(expr, env, s);
            }
            Stmt::LogLevel { .. } => {}
            // M4-10 (7.8): the fetch/post/send values are checked like a
            // Send's; the server bodies walk; the request reads carry
            // only names.
            Stmt::Fetch {
                data,
                headers,
                query,
                ..
            } => {
                if let Some(d) = data {
                    self.check_expr(d, env, s);
                }
                for (_, e) in headers.iter().chain(query.iter()) {
                    self.check_expr(e, env, s);
                }
            }
            Stmt::PostTo { data, .. } => {
                self.check_expr(data, env, s);
            }
            Stmt::WsSend { value } => {
                self.check_expr(value, env, s);
            }
            Stmt::Respond { kind, .. } => match kind {
                RespondKind::Text(e) | RespondKind::Json(e) | RespondKind::Literally(e) => {
                    self.check_expr(e, env, s);
                }
                RespondKind::Status(_, Some(e)) => {
                    self.check_expr(e, env, s);
                }
                RespondKind::Status(_, None) | RespondKind::Template(_) => {}
            },
            Stmt::Serve { body, .. }
            | Stmt::WhenSomeone { body, .. }
            | Stmt::WhenLive { body, .. } => {
                self.check_stmts(body, env, s);
            }
            Stmt::PageDecl { .. } | Stmt::WsRecv { .. } => {}
            Stmt::Careful { body } => {
                self.check_stmts(body, env, s);
            }
            Stmt::WhenSignal { body, .. } | Stmt::ForEachInput { body, .. } => {
                self.check_stmts(body, env, s);
            }
            Stmt::Spread { items, body } => {
                self.check_expr(items, env, s);
                self.check_stmts(body, env, s);
            }
            // M4-5 (Appendix K 7.5): the write/append/replace value is
            // checked like a Send's (a copy into the file, logged); the
            // loop/watch bodies walk like a task's; the other file
            // sentences move nothing.
            Stmt::WriteFile { value, .. }
            | Stmt::AppendFile { value, .. }
            | Stmt::ReplaceFile { value, .. } => {
                self.check_expr(value, env, s);
            }
            Stmt::ForEachLine { body, .. } | Stmt::WhenFileChanges { body, .. } => {
                self.check_stmts(body, env, s);
            }
            // M4-6: the save value and the from-text decode source are
            // checked like the write value (a copy out, logged)
            Stmt::SaveFormat { value, .. } | Stmt::ReadFormatText { value, .. } => {
                self.check_expr(value, env, s);
            }
            Stmt::ReadFile { .. }
            | Stmt::ReadBytes { .. }
            | Stmt::ListFolder { .. }
            | Stmt::MakeFolder { .. }
            | Stmt::RemovePath { .. }
            | Stmt::MovePath { .. }
            | Stmt::DuplicatePath { .. }
            | Stmt::MakeTempFile { .. }
            | Stmt::ZipOp { .. }
            | Stmt::ReadFormat { .. } => {}
        }
    }

    /// Check the expressions of one value, killing names that are moved away
    /// (ch.28, M2-S2).
    fn check_expr(&mut self, expr: &Expr, env: &mut OwnEnv, s: Option<&'a Sentence>) {
        match &expr.e {
            E::Name(n) => {
                if let Some(v) = env.vars.get(n.as_str()) {
                    if !v.alive && is_move_kind(&v.kind) {
                        let (w, wh, fx) = t0401_parts(env, n);
                        self.err_opt("T0401", w, s, 0, 0, wh, fx);
                    }
                }
                if self.lent_live.iter().any(|x| x == n) {
                    // T0404: the value is read while its writer borrow is live (ch.29)
                    self.err_opt(
                        "T0404",
                        "A value is read while a writer is live.".to_string(),
                        s,
                        0,
                        0,
                        format!("{n} is being changed in this sentence."),
                        "End the change first.".to_string(),
                    );
                }
            }
            E::Call { name, args } => {
                let mut lent_this_call: Vec<String> = Vec::new();
                for (i, arg) in args.iter().enumerate() {
                    let mode = self
                        .funcs
                        .iter()
                        .find(|f| f.name == *name)
                        .and_then(|f| f.inputs.get(i))
                        .map(|(_, m)| *m)
                        .unwrap_or(ParamMode::Lent);
                    // T0403 first: the same name passed to two lend to change
                    // inputs is two live writers, which is the mistake. The
                    // expression walk would report the second one as a read
                    // (T0404) and stop at one error per sentence, so the
                    // two-writer case is decided here (ch.29).
                    if mode == ParamMode::LentToChange {
                        if let Some(n) = bare_name_of(arg) {
                            if lent_this_call.contains(&n) {
                                self.err_opt(
                                    "T0403",
                                    "Two unique borrows of one value are live at once.".to_string(),
                                    s,
                                    0,
                                    0,
                                    "one name passed to two lend to change inputs".to_string(),
                                    "Use one borrow at a time.".to_string(),
                                );
                                break;
                            }
                        }
                    }
                    self.check_expr(arg, env, s);
                    if let Some(n) = bare_name_of(arg) {
                        match mode {
                            ParamMode::MoveIn => {
                                if env
                                    .vars
                                    .get(n.as_str())
                                    .map_or(false, |v| is_move_kind(&v.kind))
                                {
                                    kill_name(env, &n);
                                }
                            }
                            ParamMode::LentToChange => {
                                if env.vars.get(n.as_str()).map_or(false, |v| !v.mutable) {
                                    self.err_opt(
                                        "T0407",
                                        "A fixed name is passed to a lend to change input."
                                            .to_string(),
                                        s,
                                        0,
                                        0,
                                        format!("{n} is fixed, not Changeable."),
                                        "Make it Changeable.".to_string(),
                                    );
                                }
                                // the two-writer case (T0403) is decided
                                // before the expression walk above
                                lent_this_call.push(n.clone());
                                self.lent_live.push(n);
                            }
                            ParamMode::Lent => {}
                        }
                    }
                }
            }
            E::Move(inner) | E::Share(inner) => {
                self.check_expr(inner, env, s);
                if let E::Name(n) = &inner.e {
                    if env
                        .vars
                        .get(n.as_str())
                        .map_or(false, |v| is_move_kind(&v.kind))
                    {
                        kill_name(env, &n);
                    }
                }
            }
            E::CopyOf(inner) | E::WeakShare(inner) => {
                self.check_expr(inner, env, s);
            }
            E::Binary { l, r, .. } | E::DivWhole(l, r) | E::Rem(l, r) | E::Pow(l, r) => {
                self.check_expr(l, env, s);
                self.check_expr(r, env, s);
            }
            E::RecordOf { parts, .. } | E::EnumOf { parts, .. } => {
                for (_, e) in parts {
                    self.check_expr(e, env, s);
                    if let E::Name(n) = &e.e {
                        if env.params.iter().any(|p| p == n) {
                            // T0408: a record cannot hold a borrow (ch.29)
                            self.err_opt(
                                "T0408",
                                "A record is made to hold a borrow.".to_string(),
                                s,
                                0,
                                0,
                                format!("{n} is a borrow of an input."),
                                "Give or copy the value.".to_string(),
                            );
                        }
                        if env
                            .vars
                            .get(n.as_str())
                            .map_or(false, |v| is_move_kind(&v.kind))
                        {
                            kill_name(env, &n);
                        }
                    }
                }
            }
            E::Fallback { value, default } => {
                self.check_expr(value, env, s);
                self.check_expr(default, env, s);
            }
            E::PartOf { base, .. } => {
                self.check_expr(base, env, s);
            }
            // reading a part, an item or a range reads the collection too:
            // a moved-away name is T0401 here as well (ch.28)
            E::ItemN { list, n } => {
                self.check_expr(list, env, s);
                self.check_expr(n, env, s);
            }
            E::ItemsRange { list, from, to } => {
                self.check_expr(list, env, s);
                self.check_expr(from, env, s);
                self.check_expr(to, env, s);
            }
            E::FirstOf(x) | E::LastOf(x) => {
                self.check_expr(x, env, s);
            }
            // M4-7 (7.7): the time and secret reads walk their children
            // like the other reads.
            E::MomentAt { date, .. }
            | E::InZone { base: date, .. }
            | E::TimeShift { base: date, .. }
            | E::RandomItem { list: date }
            | E::Shuffled { list: date }
            | E::HashOf(date)
            | E::SecretOf(date)
            | E::Reveal(date) => {
                self.check_expr(date, env, s);
            }
            E::DaysBetween { a, b } | E::SecondsBetween { a, b } | E::RandomRange { a, b } => {
                self.check_expr(a, env, s);
                self.check_expr(b, env, s);
            }
            E::Flat(_)
            | E::It
            | E::Them
            | E::Whole(_)
            | E::Dec(_)
            | E::Boolean(_)
            | E::Missing
            | E::Word(_)
            | E::PatWords { .. } => {}
            E::Neg(x)
            | E::Round(x, _)
            | E::Factorial(x)
            | E::CountIn(x)
            | E::Lower(x)
            | E::Upper(x)
            | E::AsWhole(x)
            | E::AsDecimal(x)
            | E::AsText(x)
            | E::AsNumber(x)
            | E::Sorted(x, _)
            | E::Reverse(x)
            | E::Unique(x)
            | E::Trimmed(x)
            | E::Normalized(x) => {
                self.check_expr(x, env, s);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------- cursor

#[derive(Clone)]
struct TS<'a> {
    toks: &'a [Token],
    pos: usize,
}

impl<'a> TS<'a> {
    fn new(toks: &'a [Token]) -> Self {
        TS { toks, pos: 0 }
    }
    fn peek(&self) -> Option<&Token> {
        self.toks.get(self.pos)
    }
    fn peek_next(&self) -> Option<&str> {
        self.toks.get(self.pos + 1).and_then(|t| match t {
            Token::Word { lower, .. } => Some(lower.as_str()),
            _ => None,
        })
    }
    fn peek_word(&self) -> Option<&str> {
        match self.toks.get(self.pos) {
            Some(Token::Word { lower, .. }) => Some(lower.as_str()),
            _ => None,
        }
    }
    fn peek_number(&self) -> Option<i64> {
        match self.toks.get(self.pos) {
            Some(Token::Whole { value }) => Some(*value),
            _ => None,
        }
    }
    fn consume_word(&mut self, w: &str) -> bool {
        if self.peek_word() == Some(w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn rest_without_period(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        while self.pos < self.toks.len() {
            match &self.toks[self.pos] {
                Token::Period | Token::Eof => break,
                t => {
                    out.push(t.clone());
                    self.pos += 1;
                }
            }
        }
        out
    }
    fn rest_until_one_line_action(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        while self.pos < self.toks.len() {
            match &self.toks[self.pos] {
                Token::Period | Token::Eof => break,
                Token::Word { lower, .. } if is_one_line_action(lower) => break,
                t => {
                    out.push(t.clone());
                    self.pos += 1;
                }
            }
        }
        out
    }
    fn rest_until_word(&mut self, stop: &str) -> Vec<Token> {
        let mut out = Vec::new();
        while self.pos < self.toks.len() {
            match &self.toks[self.pos] {
                Token::Period | Token::Eof => break,
                Token::Word { lower, .. } if lower == stop => break,
                t => {
                    out.push(t.clone());
                    self.pos += 1;
                }
            }
        }
        out
    }
}

fn is_one_line_action(word: &str) -> bool {
    matches!(
        word,
        "say"
            | "set"
            | "stop"
            | "skip"
            | "give"
            | "hand"
            | "fail"
            | "exit"
            | "add"
            | "remove"
            | "put"
            | "send"
    )
}

/// Split trailing Say modifiers (`to N places` / `width N`) off the content.
fn split_trailing_mods(toks: Vec<Token>) -> (Vec<Token>, Vec<Token>) {
    for i in 0..toks.len() {
        let is_to = matches!(&toks[i], Token::Word { lower, .. } if lower == "to");
        let is_width = matches!(&toks[i], Token::Word { lower, .. } if lower == "width");
        if is_to {
            if let Some(Token::Whole { .. }) = toks.get(i + 1) {
                if let Some(Token::Word { lower, .. }) = toks.get(i + 2) {
                    if lower == "places" || lower == "place" {
                        return (toks[..i].to_vec(), toks[i..].to_vec());
                    }
                }
            }
        }
        if is_width {
            if let Some(Token::Whole { .. }) = toks.get(i + 1) {
                return (toks[..i].to_vec(), toks[i..].to_vec());
            }
        }
    }
    (toks, Vec::new())
}
