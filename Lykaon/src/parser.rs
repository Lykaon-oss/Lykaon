//! Parser for M1a sentences: recursive descent over the pattern table (Appendix B, p.201).

use crate::diagnostics::Diagnostic;
use crate::lexer::{Lexer, Token, hard_words};
use crate::pre_scan::NameTable;
use crate::splitter::Sentence;

/// One-line action words that end an If/Repeat one-line question (G20).
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

fn diag(
    code: &'static str,
    what: &str,
    file: &str,
    line: usize,
    sentence: &str,
    lo: usize,
    hi: usize,
    why: &str,
    fix: &str,
) -> Diagnostic {
    Diagnostic::error(
        code,
        what.to_string(),
        file.to_string(),
        line,
        sentence.to_string(),
        lo,
        hi,
        why.to_string(),
        fix.to_string(),
    )
}

/// Parse a whole block of sentences. Returns diagnostics.
/// `all` is the flat sentence vec; `indices` are the indices to iterate.
pub fn parse_block(
    all: &[Sentence],
    indices: &[usize],
    names: &NameTable,
    file: &str,
    in_loop: bool,
) -> Vec<Diagnostic> {
    parse_block_fn(all, indices, names, file, in_loop, false)
}

pub fn parse_block_fn(
    all: &[Sentence],
    indices: &[usize],
    names: &NameTable,
    file: &str,
    in_loop: bool,
    in_fn: bool,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let mut i = 0;
    while i < indices.len() {
        let idx = indices[i];
        let s = &all[idx];
        let (toks, _) = Lexer::new(&s.text).tokenize();
        let first_word = toks
            .first()
            .and_then(|t| match t {
                Token::Word { lower, .. } => Some(lower.as_str()),
                _ => None,
            })
            .unwrap_or("");
        match first_word {
            "if" => {
                diags.extend(parse_if(all, indices, &mut i, names, file, in_loop, in_fn));
            }
            "otherwise" => {
                diags.push(diag(
                    "T0112",
                    "Otherwise without If.",
                    file,
                    s.line,
                    &s.text,
                    0,
                    s.text.len(),
                    "Otherwise has no If at the same indentation.",
                    "Put it right after an If.",
                ));
                i += 1;
            }
            "to" => {
                diags.extend(parse_to(s, all, names, file, in_loop));
                i += 1;
            }
            "for" => {
                diags.extend(parse_for(s, all, names, file, in_loop, in_fn));
                i += 1;
            }
            "give" => {
                // Give back <value>. ends a block function (T0115).
                // Give <value>. moves a value (M2, ch.30) and is not give
                // back: only the back spelling is tied to a function.
                let second = s
                    .text
                    .split_whitespace()
                    .nth(1)
                    .unwrap_or("")
                    .trim_end_matches('.')
                    .to_ascii_lowercase();
                if !in_fn && second == "back" {
                    diags.push(diag(
                        "T0115",
                        "Give back outside a function.",
                        file,
                        s.line,
                        &s.text,
                        0,
                        s.text.len(),
                        "Give back is not inside a function.",
                        "Put it inside a function block.",
                    ));
                }
                i += 1;
            }
            _ => {
                // Under "Say lines." the indented lines are raw text, not
                // sentences (Ch.10): only the opener itself is parsed.
                if s.is_raw_text {
                    i += 1;
                    continue;
                }
                diags.extend(parse_sentence(s, names, file, in_loop, in_fn, all));
                i += 1;
            }
        }
    }
    diags
}

fn parse_if(
    all: &[Sentence],
    indices: &[usize],
    i: &mut usize,
    names: &NameTable,
    file: &str,
    in_loop: bool,
    in_fn: bool,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let idx = indices[*i];
    let s = &all[idx];
    let line = s.line;
    let text = &s.text;
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("if"); // consume "if"

    // "If that fails use X." is the fallback sentence (Chapter 17). It has no
    // condition; the value after "use" is checked by the semantic layer.
    let lower_words: Vec<String> = toks
        .iter()
        .filter_map(|t| match t {
            Token::Word { lower, .. } => Some(lower.clone()),
            _ => None,
        })
        .collect();
    if lower_words.len() >= 3 && lower_words[1] == "that" && lower_words[2] == "fails" {
        *i += 1;
        return diags;
    }

    let has_block = !s.children.is_empty();

    if has_block {
        let cond_toks = ts.rest_without_period();
        parse_condition(&cond_toks, text, file, line, names, &mut diags);
        diags.extend(parse_block_fn(
            all,
            &s.children,
            names,
            file,
            in_loop,
            in_fn,
        ));
        *i += 1;
        // consume otherwise / otherwise-if siblings
        while *i < indices.len() {
            let os_idx = indices[*i];
            let os = &all[os_idx];
            let (ot, _) = Lexer::new(&os.text).tokenize();
            let first = ot
                .first()
                .and_then(|t| match t {
                    Token::Word { lower, .. } => Some(lower.as_str()),
                    _ => None,
                })
                .unwrap_or("");
            if first == "otherwise" {
                let mut ots = TS::new(&ot);
                ots.consume_word("otherwise");
                if ots.peek_word() == Some("if") {
                    ots.pos += 1;
                    let ocond = ots.rest_without_period();
                    parse_condition(&ocond, &os.text, file, os.line, names, &mut diags);
                }
                diags.extend(parse_block_fn(
                    all,
                    &os.children,
                    names,
                    file,
                    in_loop,
                    in_fn,
                ));
                *i += 1;
            } else {
                break;
            }
        }
    } else {
        let cond_toks = ts.rest_until_one_line_action();
        parse_condition(&cond_toks, text, file, line, names, &mut diags);
        let rest = ts.rest_without_period();
        if !rest.is_empty() {
            parse_one_line_stmt(&rest, text, file, line, names, in_loop, &mut diags);
        }
        *i += 1;
        // a one-line If still pairs with a following Otherwise (Ch.9)
        while *i < indices.len() {
            let os_idx = indices[*i];
            let os = &all[os_idx];
            let (ot, _) = Lexer::new(&os.text).tokenize();
            let first = ot
                .first()
                .and_then(|t| match t {
                    Token::Word { lower, .. } => Some(lower.as_str()),
                    _ => None,
                })
                .unwrap_or("");
            if first != "otherwise" {
                break;
            }
            let mut ots = TS::new(&ot);
            ots.consume_word("otherwise");
            if ots.peek_word() == Some("if") {
                ots.pos += 1;
                let ocond = ots.rest_until_one_line_action();
                parse_condition(&ocond, &os.text, file, os.line, names, &mut diags);
                let orest = ots.rest_without_period();
                if !orest.is_empty() {
                    parse_one_line_stmt(
                        &orest, &os.text, file, os.line, names, in_loop, &mut diags,
                    );
                }
            }
            *i += 1;
        }
    }
    diags
}

/// Parse one sentence (non-if, non-otherwise). Returns diagnostics.
pub fn parse_sentence(
    s: &Sentence,
    names: &NameTable,
    file: &str,
    in_loop: bool,
    in_fn: bool,
    _all: &[Sentence],
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    if s.is_raw_text {
        return diags;
    }
    let text = &s.text;
    // T0012 missing final period
    if !text.ends_with('.') {
        diags.push(diag(
            "T0012",
            "Missing final period.",
            file,
            s.line,
            text,
            text.len(),
            text.len(),
            "A sentence does not end with a period.",
            "Add a period at the end of the line.",
        ));
        return diags;
    }
    // The lexer refuses quotes, commas, invalid characters and digit-led
    // names; its diagnostic surfaces here (raw-text sentences and the
    // text-taking words Note/About keep their punctuation, ch.3, and are
    // not lexed strictly).
    let fw = text
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_ascii_lowercase();
    let text_taking = matches!(fw.as_str(), "note" | "about");
    // the Run sentence's own name rules live in the semantic layer (its
    // lexer-error handling is the designed T0113)
    let sem_owns = fw == "run";
    // a tab is the splitter's own T0001 (one error per mistake, ch.66):
    // the sentence check stays out of its way
    if !s.is_raw_text && !text_taking && !sem_owns && !text.contains('\t') {
        if let Some(mut d) = Lexer::new(text).tokenize().1 {
            d.file = file.to_string();
            d.line = s.line;
            diags.push(d);
            return diags;
        }
    }
    let (toks, _) = Lexer::new(text).tokenize();
    let ts = TS::new(&toks);
    let first_word = ts.peek_word().unwrap_or("");
    match first_word {
        "note" => {
            // case-insensitive strip of "note"
            let stripped = text.trim_start();
            let stripped = stripped
                .strip_prefix(|c: char| c.to_ascii_lowercase() == 'n')
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 'o'))
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 't'))
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 'e'))
                .unwrap_or(stripped);
            let rest = stripped.trim_start();
            if rest.is_empty() || rest == "." {
                diags.push(diag(
                    "T0016",
                    "Text missing.",
                    file,
                    s.line,
                    text,
                    0,
                    4,
                    "A word that takes text has none.",
                    "Write the text after the word.",
                ));
            }
        }
        "about" => {
            let stripped = text.trim_start();
            let stripped = stripped
                .strip_prefix(|c: char| c.to_ascii_lowercase() == 'a')
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 'b'))
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 'u'))
                .and_then(|s| s.strip_prefix(|c: char| c.to_ascii_lowercase() == 't'))
                .unwrap_or(stripped);
            let rest = stripped.trim_start();
            if rest.is_empty() || rest == "." {
                diags.push(diag(
                    "T0016",
                    "Text missing.",
                    file,
                    s.line,
                    text,
                    0,
                    5,
                    "A word that takes text has none.",
                    "Write the text after the word.",
                ));
            }
        }
        "example" => {
            // T0154 (M2-S57): Example is not under About (the About's own
            // Example children are not walked by the pre-scan)
            diags.push(diag(
                "T0154",
                "Example outside About.",
                file,
                s.line,
                text,
                0,
                7,
                "Example is not under About.",
                "Put it under About.",
            ));
        }
        "changeable" => {
            diags.extend(parse_changeable(text, file, s.line, names));
        }
        "constant" => {
            diags.extend(parse_constant(text, file, s.line, names));
        }
        // record and enum type declarations (ch.20-21); the checks live in the
        // type layer
        "a" | "an" => {}
        // Look at / When (ch.21); the checks live in the type layer
        "look" => {}
        "when" => {
            // M4-5 (Appendix K 7.5): "When <file_ref> changes." owns an
            // indented body, walked like a timer body (in_loop because
            // Stop. cancels the watcher); the plain When checks live in
            // the type layer.
            // M4-8 (Appendix K 7.10): "When signal <name> arrives." owns
            // an indented body too (the block is a task, M4-S79; the
            // semantic layer checks the shape and the capture rules).
            let words: Vec<&str> = text.split_whitespace().collect();
            let second = words.get(1).copied().unwrap_or("").to_ascii_lowercase();
            let last = words
                .last()
                .copied()
                .unwrap_or("")
                .trim_end_matches('.')
                .to_ascii_lowercase();
            if (second == "file" || second == "folder") && last == "changes" {
                if !s.children.is_empty() {
                    diags.extend(parse_block_fn(_all, &s.children, names, file, true, true));
                }
            } else if second == "signal" && last == "arrives" {
                if !s.children.is_empty() {
                    diags.extend(parse_block_fn(_all, &s.children, names, file, false, true));
                }
            }
        }
        "say" => {
            diags.extend(parse_say(text, file, s.line, names));
        }
        // M4-9 (7.12): Log LEVEL TEXT. - the level word and the raw
        // text are checked in the semantic layer (the text is raw, so
        // the Say shape pre-checks would raise false ambiguities on it)
        "log" => {}
        // M4-10 (7.8): the network sentences and Be careful. are checked
        // in the semantic layer (the shapes are the sem layer's)
        "fetch" | "post" | "respond" | "serve" | "page" | "be" => {}
        "ask" => {
            diags.extend(parse_ask(text, file, s.line, names));
        }
        "set" => {
            diags.extend(parse_set(text, file, s.line, names));
        }
        "put" => {
            diags.extend(parse_put(text, file, s.line, names));
        }
        "remove" => {
            // M4-5 (Appendix K 7.5): Remove file <ref>. / Remove folder
            // <ref>. is not a collection sentence; it is checked in the
            // semantic layer. The plain Remove from keeps its check.
            let (rt, _) = Lexer::new(text).tokenize();
            let is_path = matches!(
                rt.get(1),
                Some(Token::Word { lower, .. }) if lower == "file" || lower == "folder"
            );
            if !is_path {
                diags.extend(parse_remove(text, file, s.line, names));
            }
        }
        "stop" => {
            // M4 (Appendix K): Stop task NAME. is a task cancel request,
            // not a loop Stop; the checks live in the semantic layer.
            let words: Vec<&str> = text.split_whitespace().collect();
            let is_stop_task = words.len() > 1 && words[1].eq_ignore_ascii_case("task");
            if !in_loop && !is_stop_task {
                diags.push(diag(
                    "T0113",
                    "Stop outside a loop.",
                    file,
                    s.line,
                    text,
                    0,
                    4,
                    "Stop. is not inside a loop.",
                    "Use it inside Repeat or For each.",
                ));
            }
        }
        "skip" => {
            if !in_loop {
                diags.push(diag(
                    "T0114",
                    "Skip outside a loop.",
                    file,
                    s.line,
                    text,
                    0,
                    4,
                    "Skip. is not inside a loop.",
                    "Use it inside Repeat or For each.",
                ));
            }
        }
        // Try / Fail / Pass failure up (ch.19): the checks live in the type layer
        "try" => {}
        "fail" => {}
        "pass" => {}
        // Close / Share / Weak share (ch.28-31): the checks live in the type layer
        "close" => {}
        "share" => {}
        "weak" => {}
        // Modules and tests (ch.36, 38): the checks live in the type layer
        "use" | "pretend" => {}
        "test" | "check" => {}
        "repeat" => {
            diags.extend(parse_repeat(s, names, file, in_loop, in_fn, _all));
        }
        "give" => {
            // Give back <value>. ends a block function (T0115); Give
            // <value>. moves a value (M2) and is not give back
            let second = text
                .split_whitespace()
                .nth(1)
                .unwrap_or("")
                .trim_end_matches('.')
                .to_ascii_lowercase();
            if !in_fn && second == "back" {
                diags.push(diag(
                    "T0115",
                    "Give back outside a function.",
                    file,
                    s.line,
                    text,
                    0,
                    text.len(),
                    "Give back is not inside a function.",
                    "Put it inside a function block.",
                ));
            }
        }
        // M3: Hand back is a generator sentence (ch.25); contracts and tags
        // are checked in the semantic layer (ch.64, M3-G24).
        "hand" => {
            if !in_fn {
                diags.push(diag(
                    "T0116",
                    "Hand back outside a function.",
                    file,
                    s.line,
                    text,
                    0,
                    text.len(),
                    "Hand back is not inside a function.",
                    "Put it inside a generator function.",
                ));
            }
        }
        "requires" | "ensures" | "always" | "tagged" | "anything" | "by" => {}
        // Ch.16/76: Combine, Apply, Add are checked in the semantic layer.
        "combine" | "apply" | "add" => {}
        // M4 (Appendix K): the task and pause sentences. Start task and
        // Do these together own indented bodies: the body is walked here
        // (a task body grants in_fn, because Give back is its result);
        // Wait for / Sleep for are checked in the semantic layer.
        "start" => {
            let words: Vec<&str> = text.split_whitespace().collect();
            if words.len() > 1 && words[1].eq_ignore_ascii_case("task") {
                diags.extend(parse_block_fn(_all, &s.children, names, file, false, true));
            }
        }
        "do" => {
            let words: Vec<&str> = text.split_whitespace().collect();
            if words.len() > 2
                && words[1].eq_ignore_ascii_case("these")
                && words[2].eq_ignore_ascii_case("together")
            {
                diags.extend(parse_block_fn(
                    _all,
                    &s.children,
                    names,
                    file,
                    in_loop,
                    in_fn,
                ));
            }
        }
        "wait" | "sleep" => {}
        // M4-4 (Appendix K 7.3/7.4): the timer and spread sentences own
        // indented bodies (After/Every NUMBER unit. and Spread each of
        // LIST over workers.); the body is walked like a task body.
        "after" | "every" | "spread" => {
            if !s.children.is_empty() {
                // M4-S26: Stop. inside an Every round ends it, and a Stop
                // inside a Spread round ends the spread; walk with
                // in_loop=true so the pre-scan does not refuse it.
                diags.extend(parse_block_fn(_all, &s.children, names, file, true, true));
            }
        }
        // M4 (Appendix K): the channel sentences are checked in the
        // semantic layer (they carry definitions and channel names).
        "send" | "receive" => {}
        // M4-5 (Appendix K 7.5): the file verbs. Name, kind and file-gate
        // checks live in the semantic layer; the When-file body walk is
        // done by the when arm above, the For-each-line body by for.
        "write" | "append" | "read" | "replace" | "make" | "move" | "duplicate" | "list"
        | "zip" | "unzip" | "gzip" => {}
        // M4-6 (Appendix K 7.6): Save <value> as <format> to file <name>.
        // sits with the file verbs (the as-format split is semantic
        // work); a `save` that starts a definition stays a definition
        // only when no as-format follows - `Save x is ...` is a name
        // clash the layer below reports.
        "save" => {}
        // M4-8 (Appendix K 7.10/7.11): the system sentences (Run/Exit, the
        // T0171 path rule and the 0..255 code range) and the tool
        // declarations (Takes/Option, placement and kinds) are checked in
        // the semantic layer.
        "run" | "exit" | "takes" | "option" => {}
        _ => {
            // A sentence of a later milestone is T0509 from the semantic
            // layer (Appendix K 1.1), not a T0110 action-word complaint
            // here - the pre-scan stays out of the way.
            if crate::sem::later_milestone_shape(text).is_some() {
                return diags;
            }
            // Check for definition: <name> is ...
            // Tokenize words manually to handle multi-word names
            let mut words: Vec<&str> = text.split_whitespace().collect();
            // Strip trailing periods from words
            for w in words.iter_mut() {
                *w = w.trim_end_matches('.');
            }
            // Remove empty words
            words.retain(|w| !w.is_empty());
            if words.len() >= 2 && words.iter().any(|w| w.eq_ignore_ascii_case("is")) {
                let name_end = words
                    .iter()
                    .position(|w| w.eq_ignore_ascii_case("is"))
                    .unwrap_or(1);
                // the articles the/a/an are removed from code (ch.4):
                // `The words is ...` defines `words`
                let start = words
                    .first()
                    .map_or(0, |w| match w.to_ascii_lowercase().as_str() {
                        "the" | "a" | "an" => 1,
                        _ => 0,
                    });
                if name_end == 0 {
                    // T0103: the definition has no name (`is 5.`)
                    diags.push(diag(
                        "T0103",
                        "Empty name.",
                        file,
                        s.line,
                        text,
                        0,
                        0,
                        "A definition has no name.",
                        "Write a name before is.",
                    ));
                } else {
                    let name = if name_end > start {
                        words[start..name_end].join(" ")
                    } else {
                        String::new()
                    };
                    if name.is_empty() {
                        diags.push(diag(
                            "T0103",
                            "Empty name.",
                            file,
                            s.line,
                            text,
                            0,
                            0,
                            "A definition has no name.",
                            "Write a name before is.",
                        ));
                    } else {
                        validate_name(&name, text, file, s.line, names, &mut diags);
                        let val_start = name_end + 1;
                        if val_start >= words.len() {
                            diags.push(diag(
                                "T0107",
                                "Definition without a value.",
                                file,
                                s.line,
                                text,
                                text.len(),
                                text.len(),
                                "is has nothing after it.",
                                "Write the value after is.",
                            ));
                        } else {
                            parse_value_expr(
                                &words[val_start..],
                                text,
                                file,
                                s.line,
                                names,
                                &mut diags,
                            );
                        }
                    }
                }
            } else {
                diags.push(diag("T0110", "No action word.", file, s.line, text, 0, first_word.len(),
                    "The first word of a sentence is not an action word, a declaration word or a defined name.",
                    "Start with an action word."));
            }
        }
    }
    diags
}

// ---------- changeable / constant ----------

fn parse_changeable(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("changeable");
    let name_tok = ts.consume();
    match name_tok {
        Some(Token::Word {
            text: original,
            lower,
        }) => {
            validate_word_name(&original, &lower, text, file, line, names, &mut diags);
            if !ts.consume_word("is") {
                diags.push(diag(
                    "T0106",
                    "Definition without is.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos,
                    "A sentence begins with a name but has no is.",
                    "Write Name is value.",
                ));
            }
            if ts.pos < ts.toks.len() && !matches!(ts.toks[ts.pos], Token::Period | Token::Eof) {
                parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
            } else {
                diags.push(diag(
                    "T0107",
                    "Definition without a value.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos,
                    "is has nothing after it.",
                    "Write the value after is.",
                ));
            }
        }
        _ => {
            diags.push(diag(
                "T0103",
                "Empty name.",
                file,
                line,
                text,
                0,
                0,
                "A definition has no name.",
                "Write a name before is.",
            ));
        }
    }
    diags
}

fn parse_constant(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("constant");
    let name_tok = ts.consume();
    match name_tok {
        Some(Token::Word {
            text: original,
            lower,
        }) => {
            validate_word_name(&original, &lower, text, file, line, names, &mut diags);
            if !ts.consume_word("is") {
                diags.push(diag(
                    "T0106",
                    "Definition without is.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos,
                    "A sentence begins with a name but has no is.",
                    "Write Name is value.",
                ));
            }
            if ts.pos < ts.toks.len() {
                match &ts.toks[ts.pos] {
                    Token::Whole { .. }
                    | Token::Decimal { .. }
                    | Token::Negative { .. }
                    | Token::YesNo { .. }
                    | Token::Missing
                    | Token::Nothing => {
                        ts.pos += 1;
                    }
                    _ => {
                        diags.push(diag(
                            "T0206",
                            "Constant is not a literal.",
                            file,
                            line,
                            text,
                            ts.pos,
                            ts.pos + 1,
                            "A Constant holds a calculation.",
                            "Use a literal.",
                        ));
                    }
                }
                // Extra tokens after the literal: constant holds a calculation
                while ts.pos < ts.toks.len()
                    && !matches!(ts.toks[ts.pos], Token::Period | Token::Eof)
                {
                    diags.push(diag(
                        "T0206",
                        "Constant is not a literal.",
                        file,
                        line,
                        text,
                        ts.pos,
                        ts.pos + 1,
                        "A Constant holds a calculation.",
                        "Use a literal.",
                    ));
                    ts.pos += 1;
                }
            } else {
                diags.push(diag(
                    "T0107",
                    "Definition without a value.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos,
                    "is has nothing after it.",
                    "Write the value after is.",
                ));
            }
        }
        _ => {
            diags.push(diag(
                "T0103",
                "Empty name.",
                file,
                line,
                text,
                0,
                0,
                "A definition has no name.",
                "Write a name before is.",
            ));
        }
    }
    diags
}

// ---------- say ----------

fn parse_say(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("say");
    if ts.pos >= ts.toks.len() || matches!(ts.toks[ts.pos], Token::Period | Token::Eof) {
        diags.push(diag(
            "T0017",
            "Nothing to print.",
            file,
            line,
            text,
            3,
            3,
            "Say has nothing after it.",
            "Write what to print.",
        ));
        return diags;
    }
    if ts.peek_word() == Some("if") {
        ts.pos += 1;
        let cond = ts.rest_without_period();
        parse_condition(&cond, text, file, line, names, &mut diags);
        return diags;
    }
    if ts.peek_word() == Some("lines") {
        return diags;
    }
    // Ch.65: "Say first 2 of numbers sorted." reads two ways (postfix word
    // after the hole of a pattern) -> T0130.
    let mut head: Vec<String> = Vec::new();
    let mut name = String::new();
    let mut postfix = String::new();
    let mut stage = 0; // 0 = before of, 1 = name, 2 = postfix
    let mut has_num = false;
    for t in ts.toks[ts.pos..].iter() {
        match t {
            Token::Word { lower, .. } => match stage {
                0 => {
                    if lower == "of" && !head.is_empty() {
                        stage = 1;
                    } else {
                        head.push(lower.clone());
                    }
                }
                1 => {
                    name = lower.clone();
                    stage = 2;
                }
                _ => {
                    postfix = lower.clone();
                    break;
                }
            },
            Token::Whole { value } => {
                if stage == 0 {
                    head.push(value.to_string());
                    has_num = true;
                }
            }
            Token::Negative { value } => {
                if stage == 0 {
                    head.push(format!("minus {value}"));
                    has_num = true;
                }
            }
            _ => {}
        }
    }
    const POSTFIX: [&str; 5] = ["sorted", "reversed", "unique", "trimmed", "backwards"];
    if has_num && POSTFIX.contains(&postfix.as_str()) {
        let head_s = head.join(" ");
        let why = format!(
            "it can mean the {head_s} of {name}, {postfix}, or the {head_s} of {name} {postfix}."
        );
        diags.push(diag(
            "T0130",
            "This sentence can be read two ways.",
            file,
            line,
            text,
            0,
            text.len(),
            &why,
            "Split it into two sentences.",
        ));
        return diags;
    }
    while ts.pos < ts.toks.len() {
        match ts.peek_word() {
            Some("literally") => {
                ts.pos += 1;
            }
            Some("without") => {
                ts.pos += 1;
                if ts.peek_word() == Some("newline") {
                    ts.pos += 1;
                }
            }
            _ => break,
        }
    }
    parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
    diags
}

// ---------- ask ----------

fn parse_ask(text: &str, file: &str, line: usize, _names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("ask");
    let _ = ts.consume(); // name
    if ts.peek_word() == Some("as") {
        ts.pos += 1;
        if let Some(w) = ts.peek_word() {
            match w {
                "number" | "decimal" | "text" => {
                    ts.pos += 1;
                }
                _ => {
                    diags.push(diag(
                        "T0509",
                        "Feature arrives later.",
                        file,
                        line,
                        text,
                        ts.pos,
                        ts.pos + w.len(),
                        "A sentence belongs to a later milestone and is not yet implemented.",
                        "Wait for the milestone.",
                    ));
                    ts.pos += 1;
                }
            }
        }
    }
    diags
}

// ---------- set ----------

fn parse_set(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("set");
    let _ = ts.consume(); // place
    if ts.peek_word() == Some("to") {
        ts.pos += 1;
    }
    if ts.pos >= ts.toks.len() || matches!(ts.toks[ts.pos], Token::Period | Token::Eof) {
        diags.push(diag(
            "T0108",
            "Value expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "A word that needs a value is followed by the end of the sentence.",
            "Write the value.",
        ));
    } else {
        parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
    }
    diags
}

// ---------- put / remove ----------

/// Put <value> in <map> under <key>.
fn parse_put(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("put");
    let value_toks = ts.rest_until_word("in");
    if value_toks.is_empty() {
        diags.push(diag(
            "T0108",
            "Value expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Put needs a value to store.",
            "Write the value after Put.",
        ));
        return diags;
    }
    let mut vts = TS::new(&value_toks);
    parse_expr_tokens(&mut vts, text, file, line, names, &mut diags);
    if !ts.consume_word("in") {
        diags.push(diag(
            "T0108",
            "Map name expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Put needs the map the value goes into.",
            "Write in <map> after the value.",
        ));
        return diags;
    }
    let _map = match ts.peek() {
        Some(Token::Word { .. }) => {
            ts.pos += 1;
            true
        }
        _ => false,
    };
    if !_map {
        diags.push(diag(
            "T0108",
            "Map name expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Put needs the name of the map.",
            "Write the map name after in.",
        ));
        return diags;
    }
    if ts.consume_word("under") {
        let key_toks = ts.rest_without_period();
        if key_toks.is_empty() {
            diags.push(diag(
                "T0108",
                "Key expected.",
                file,
                line,
                text,
                ts.pos,
                ts.pos,
                "Put needs the key the value goes under.",
                "Write the key after under.",
            ));
        } else {
            parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
        }
    }
    diags
}

/// Remove <value> from <coll>.  or  Remove first from <coll>.
fn parse_remove(text: &str, file: &str, line: usize, names: &NameTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("remove");
    if ts.peek_word() == Some("first") {
        ts.pos += 1;
        if !ts.consume_word("from") {
            diags.push(diag(
                "T0108",
                "Collection name expected.",
                file,
                line,
                text,
                ts.pos,
                ts.pos,
                "Remove first needs the collection.",
                "Write from <collection> after first.",
            ));
            return diags;
        }
        let _coll = match ts.peek() {
            Some(Token::Word { .. }) => {
                ts.pos += 1;
                true
            }
            _ => false,
        };
        if !_coll {
            diags.push(diag(
                "T0108",
                "Collection name expected.",
                file,
                line,
                text,
                ts.pos,
                ts.pos,
                "Remove first needs the name of the collection.",
                "Write the collection name after from.",
            ));
        }
        return diags;
    }
    let value_toks = ts.rest_until_word("from");
    if value_toks.is_empty() {
        diags.push(diag(
            "T0108",
            "Value expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Remove needs a value or the word first.",
            "Write Remove <value> from <collection>.",
        ));
        return diags;
    }
    let mut vts = TS::new(&value_toks);
    parse_expr_tokens(&mut vts, text, file, line, names, &mut diags);
    if !ts.consume_word("from") {
        diags.push(diag(
            "T0108",
            "Collection name expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Remove needs the collection the value comes from.",
            "Write from <collection> after the value.",
        ));
        return diags;
    }
    let _coll = match ts.peek() {
        Some(Token::Word { .. }) => {
            ts.pos += 1;
            true
        }
        _ => false,
    };
    if !_coll {
        diags.push(diag(
            "T0108",
            "Collection name expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "Remove needs the name of the collection.",
            "Write the collection name after from.",
        ));
    }
    diags
}

// ---------- repeat ----------

fn parse_repeat(
    s: &Sentence,
    names: &NameTable,
    file: &str,
    _in_loop: bool,
    in_fn: bool,
    all: &[Sentence],
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let text = &s.text;
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    ts.consume_word("repeat");
    if ts.pos >= ts.toks.len() {
        return diags;
    }
    match &ts.toks[ts.pos] {
        Token::Whole { value } => {
            if *value < 0 {
                diags.push(diag(
                    "T0122",
                    "Bad repeat count.",
                    file,
                    s.line,
                    text,
                    ts.pos,
                    ts.pos + 5,
                    "Repeat has a negative or decimal count.",
                    "Use a whole number of 0 or more.",
                ));
            }
            ts.pos += 1;
            ts.consume_word("times");
            if ts.pos < ts.toks.len() && matches!(ts.toks[ts.pos], Token::Period | Token::Eof) {
                diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
            } else {
                let rest = ts.rest_without_period();
                parse_one_line_stmt(&rest, text, file, s.line, names, true, &mut diags);
            }
        }
        Token::Word { lower, .. } if lower == "while" => {
            // M1b: Repeat while <condition>. with an indented body.
            ts.pos += 1;
            let cond_toks = ts.rest_without_period();
            parse_condition(&cond_toks, text, file, s.line, names, &mut diags);
            diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
        }
        Token::Word { lower, .. } if lower == "forever" => {
            ts.pos += 1;
            if ts.pos < ts.toks.len() && matches!(ts.toks[ts.pos], Token::Period | Token::Eof) {
                diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
            }
        }
        Token::Decimal { .. } | Token::Negative { .. } => {
            diags.push(diag(
                "T0122",
                "Bad repeat count.",
                file,
                s.line,
                text,
                ts.pos,
                ts.pos + 5,
                "Repeat has a negative or decimal count.",
                "Use a whole number of 0 or more.",
            ));
        }
        _ => {}
    }
    diags
}

// ---------- to (functions) and for each ----------

/// To <name> <input> [with <input>]... [defaulting to <value>]
///   [can fail] [give <expr>.]        (one-line form)
/// To <name> <input> [with <input>]... .   (block form, body indented)
fn parse_to(
    s: &Sentence,
    all: &[Sentence],
    names: &NameTable,
    file: &str,
    _in_loop: bool,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let text = &s.text;
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    let line = s.line;
    ts.consume_word("to");
    // function name: one word
    match ts.peek() {
        Some(Token::Word {
            text: original,
            lower,
        }) => {
            validate_word_name(original, lower, text, file, line, names, &mut diags);
            ts.pos += 1;
        }
        _ => {
            diags.push(diag(
                "T0103",
                "Empty name.",
                file,
                line,
                text,
                2,
                2,
                "A function definition has no name after To.",
                "Write the name after To.",
            ));
            return diags;
        }
    }
    // first input is required: the word straight after the name
    match ts.peek_word() {
        Some("lend") => {
            // To pad lend to change items. (Ch.76): lend is a mode marker,
            // not a name; the input is the word after change.
            ts.pos += 1;
            if ts.consume_word("to") && ts.consume_word("change") {
                match ts.peek_word() {
                    Some(w) => {
                        validate_word_name(
                            &w.to_string(),
                            &w.to_string(),
                            text,
                            file,
                            line,
                            names,
                            &mut diags,
                        );
                        ts.pos += 1;
                    }
                    _ => {
                        diags.push(diag(
                            "T0103",
                            "Empty name.",
                            file,
                            line,
                            text,
                            ts.pos,
                            ts.pos,
                            "lend to change has no input name after it.",
                            "Write the input after change.",
                        ));
                    }
                }
            }
        }
        Some("give") => {
            // To f give items. (Ch.28): the input is moved in; the name is
            // the word after give. "give back" is a result, not an input.
            // The one-line value form `To f give 5.` has no input name
            // (the value is not a name): the semantic layer's T0157 owns
            // that case, so a non-name after give is not a T0103 here.
            ts.pos += 1;
            if ts.peek_word() != Some("back") {
                if let Some(w) = ts.peek_word() {
                    if !matches!(w, "with" | "can" | "defaulting" | "as" | "give") {
                        validate_word_name(
                            &w.to_string(),
                            &w.to_string(),
                            text,
                            file,
                            line,
                            names,
                            &mut diags,
                        );
                        ts.pos += 1;
                    }
                }
            }
        }
        Some(w) if w != "give" && w != "with" && w != "can" && w != "as" => {
            validate_word_name(
                &w.to_string(),
                &w.to_string(),
                text,
                file,
                line,
                names,
                &mut diags,
            );
            ts.pos += 1;
        }
        Some("can") | Some("as") | None => {
            // inputs allowed to be absent only with `as` (M2+) — still fine to parse
            while ts.peek_word() == Some("as") {
                ts.pos += 1;
                let _ = ts.consume();
            }
        }
        _ => {
            diags.push(diag(
                "T0103",
                "Empty name.",
                file,
                line,
                text,
                ts.pos,
                ts.pos + 1,
                "A function needs at least one input after its name.",
                "Write the input after the name.",
            ));
        }
    }
    while ts.peek_word() == Some("with") {
        ts.pos += 1;
        match ts.peek_word() {
            Some("give") => {
                // with give items. (Ch.28): a moved-in input
                ts.pos += 1;
                match ts.peek_word() {
                    Some(w) => {
                        validate_word_name(
                            &w.to_string(),
                            &w.to_string(),
                            text,
                            file,
                            line,
                            names,
                            &mut diags,
                        );
                        ts.pos += 1;
                    }
                    _ => {
                        diags.push(diag(
                            "T0103",
                            "Empty name.",
                            file,
                            line,
                            text,
                            ts.pos,
                            ts.pos,
                            "give has no input name after it.",
                            "Write the input after give.",
                        ));
                        break;
                    }
                }
            }
            Some("lend") => {
                // with lend to change items. (Ch.28/76): the same mode
                // marker as the first input, so the word after change is
                // the name (the earlier code validated `lend` itself and
                // refused the sentence as T0101).
                ts.pos += 1;
                if ts.consume_word("to") && ts.consume_word("change") {
                    match ts.peek_word() {
                        Some(w) => {
                            validate_word_name(
                                &w.to_string(),
                                &w.to_string(),
                                text,
                                file,
                                line,
                                names,
                                &mut diags,
                            );
                            ts.pos += 1;
                        }
                        _ => {
                            diags.push(diag(
                                "T0103",
                                "Empty name.",
                                file,
                                line,
                                text,
                                ts.pos,
                                ts.pos,
                                "lend to change has no input name after it.",
                                "Write the input after change.",
                            ));
                            break;
                        }
                    }
                }
            }
            Some(w) if w != "give" && w != "can" && w != "defaulting" => {
                validate_word_name(
                    &w.to_string(),
                    &w.to_string(),
                    text,
                    file,
                    line,
                    names,
                    &mut diags,
                );
                ts.pos += 1;
            }
            Some("defaulting") => break,
            _ => {
                diags.push(diag(
                    "T0103",
                    "Empty name.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos + 1,
                    "with has no input name after it.",
                    "Write the input after with.",
                ));
                break;
            }
        }
    }
    // defaulting to <value>
    if ts.peek_word() == Some("defaulting") {
        ts.pos += 1;
        if ts.consume_word("to") {
            if ts.peek_word().is_some() || !matches!(ts.peek(), Some(Token::Period)) {
                // skip the default value tokens
                parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
            }
        }
    }
    // can fail
    if ts.peek_word() == Some("can") {
        ts.pos += 1;
        ts.consume_word("fail");
    }
    // one-line give
    if ts.peek_word() == Some("give") {
        ts.pos += 1;
        if !matches!(ts.peek(), Some(Token::Period) | Some(Token::Eof)) {
            parse_expr_tokens(&mut ts, text, file, line, names, &mut diags);
        }
    } else {
        // block function body (indented children)
        diags.extend(parse_block_fn(all, &s.children, names, file, false, true));
    }
    diags
}

/// For each <x> from <a> to <b>.   For each <x> in <name>.
/// Block form or one-line form.
fn parse_for(
    s: &Sentence,
    all: &[Sentence],
    names: &NameTable,
    file: &str,
    in_loop: bool,
    in_fn: bool,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    let text = &s.text;
    let (toks, _) = Lexer::new(text).tokenize();
    let mut ts = TS::new(&toks);
    let line = s.line;
    ts.consume_word("for");
    if !ts.consume_word("each") {
        diags.push(diag(
            "T0118",
            "For without each.",
            file,
            line,
            text,
            ts.pos,
            ts.pos + 3,
            "The loop starts with for each.",
            "Write For each.",
        ));
        return diags;
    }
    // loop variable
    match ts.peek_word() {
        Some(w) if w != "from" && w != "in" => {
            validate_word_name(
                &w.to_string(),
                &w.to_string(),
                text,
                file,
                line,
                names,
                &mut diags,
            );
            ts.pos += 1;
            // For each k and v in map. (Ch.12)
            if ts.peek_word() == Some("and") {
                ts.pos += 1;
                if let Some(w) = ts.peek_word() {
                    validate_word_name(
                        &w.to_string(),
                        &w.to_string(),
                        text,
                        file,
                        line,
                        names,
                        &mut diags,
                    );
                    ts.pos += 1;
                }
            }
        }
        _ => {
            diags.push(diag(
                "T0103",
                "Empty name.",
                file,
                line,
                text,
                ts.pos,
                ts.pos + 1,
                "The loop has no name after For each.",
                "Write the name after For each.",
            ));
            return diags;
        }
    }
    if ts.peek_word() == Some("from") {
        ts.pos += 1;
        let from_toks = ts.rest_until_word("to");
        parse_operand_range(&from_toks, text, file, line, names, &mut diags, "from");
        if ts.peek_word() == Some("to") {
            ts.pos += 1;
            if !s.children.is_empty() {
                // block: the rest of the line is the range end
                let to_toks = ts.rest_without_period();
                parse_operand_range(&to_toks, text, file, line, names, &mut diags, "to");
                diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
            } else {
                // one-line: range end ends at a one-line action word
                let to_toks = ts.rest_until_one_line_action();
                parse_operand_range(&to_toks, text, file, line, names, &mut diags, "to");
                let rest = ts.rest_without_period();
                if !rest.is_empty() {
                    parse_one_line_stmt(&rest, text, file, line, names, true, &mut diags);
                }
            }
        } else {
            diags.push(diag(
                "T0118",
                "For each without to.",
                file,
                line,
                text,
                ts.pos,
                ts.pos + 2,
                "The loop range has from but no to.",
                "Write from A to B.",
            ));
        }
    } else if ts.peek_word() == Some("in") {
        ts.pos += 1;
        // visiting a list: a later milestone (Ch.11). Accepted here; the
        // semantic layer reports T0509.
        let _ = ts.consume();
        if !s.children.is_empty() {
            diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
        } else {
            let rest = ts.rest_without_period();
            if !rest.is_empty() {
                parse_one_line_stmt(&rest, text, file, line, names, true, &mut diags);
            }
        }
    } else if ts.peek_word() == Some("as") {
        // M4-G16 (Appendix K 7.4): For each x as they arrive from <channel>.
        // The shape and the channel are checked in the semantic layer;
        // children are walked like any block body.
        ts.pos += 1; // as
        if ts.consume_word("they") && ts.consume_word("arrive") && ts.consume_word("from") {
            if !s.children.is_empty() {
                diags.extend(parse_block_fn(all, &s.children, names, file, true, in_fn));
            } else {
                let rest = ts.rest_without_period();
                if !rest.is_empty() {
                    parse_one_line_stmt(&rest, text, file, line, names, true, &mut diags);
                }
            }
        }
    } else {
        diags.push(diag(
            "T0118",
            "For each without from or in.",
            file,
            line,
            text,
            ts.pos,
            ts.pos + 4,
            "The loop needs from A to B or in <name>.",
            "Write from A to B.",
        ));
    }
    let _ = in_loop;
    diags
}

fn parse_operand_range(
    toks: &[Token],
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
    which: &str,
) {
    if toks.is_empty() {
        diags.push(diag(
            "T0108",
            "Value expected.",
            file,
            line,
            text,
            0,
            0,
            "A word that needs a value is followed by the end of the sentence.",
            &format!("Write the value after {which}."),
        ));
        return;
    }
    let mut ts = TS::new(toks);
    parse_operand(&mut ts, text, file, line, names, diags);
}

// ---------- expressions ----------

fn parse_expr_tokens(
    ts: &mut TS,
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    parse_operand(ts, text, file, line, names, diags);
    if let Some(op_len) = binop_len(ts.peek()) {
        ts.pos += op_len;
        parse_operand(ts, text, file, line, names, diags);
        if let Some(_) = binop_len(ts.peek()) {
            diags.push(diag(
                "T0109",
                "Two operations in one sentence.",
                file,
                line,
                text,
                ts.pos,
                ts.pos + 1,
                "A sentence chains two operations.",
                "Write each step in its own sentence.",
            ));
        }
    } else if let Some(w) = ts.peek_word() {
        if w == "rounded" {
            ts.pos += 1;
            if ts.peek_word() == Some("to") {
                ts.pos += 1;
            }
            if ts.peek_word() == Some("even") {
                ts.pos += 1;
            }
        }
    }
}

fn parse_operand(
    ts: &mut TS,
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    if ts.pos >= ts.toks.len() {
        diags.push(diag(
            "T0108",
            "Value expected.",
            file,
            line,
            text,
            ts.pos,
            ts.pos,
            "A word that needs a value is followed by the end of the sentence.",
            "Write the value.",
        ));
        return;
    }
    // a multiword defined name ("left order") is one operand
    let mut span = 1usize;
    let words: Vec<String> = ts.toks[ts.pos..]
        .iter()
        .take(4)
        .filter_map(|t| match t {
            Token::Word { lower, .. } => Some(lower.clone()),
            _ => None,
        })
        .collect();
    let mut joined = words.first().cloned().unwrap_or_default();
    for k in (1..words.len() + 1).rev() {
        joined = words[..k].join(" ");
        if names.contains(&joined) {
            span = k;
            break;
        }
        span = 1;
    }
    if span > 1 && names.contains(&joined) {
        ts.pos += span;
        return;
    }
    match &ts.toks[ts.pos] {
        Token::Whole { .. }
        | Token::Decimal { .. }
        | Token::Negative { .. }
        | Token::YesNo { .. }
        | Token::Missing
        | Token::Nothing => {
            ts.pos += 1;
        }
        Token::Word { lower, .. } => {
            let w = lower.as_str();
            if w == "that" {
                diags.push(diag(
                    "T0140",
                    "that can only be used in If that fails, Check that and Anything that can.",
                    file,
                    line,
                    text,
                    ts.pos,
                    ts.pos + w.len(),
                    "that is used outside its three phrases.",
                    "Use that only in the fixed phrases.",
                ));
                ts.pos += 1;
            } else if w == "minus" {
                ts.pos += 1;
                if ts.pos < ts.toks.len() {
                    match &ts.toks[ts.pos] {
                        Token::Whole { .. } | Token::Decimal { .. } => {
                            ts.pos += 1;
                        }
                        _ => {
                            diags.push(diag(
                                "T0006",
                                "Number spelled as letters.",
                                file,
                                line,
                                text,
                                ts.pos,
                                ts.pos + 1,
                                "A number is written as a word where a number is expected.",
                                "Write the number with digits.",
                            ));
                        }
                    }
                }
            } else if number_words().contains(&w) {
                // Number words are text in non-numeric contexts (e.g. Say one.)
                ts.pos += 1;
            } else if names.contains(w) || !hard_word(w) {
                ts.pos += 1;
            } else {
                ts.pos += 1;
            }
        }
        _ => {
            ts.pos += 1;
        }
    }
}

fn binop_len(tok: Option<&Token>) -> Option<usize> {
    match tok {
        Some(Token::Word { lower, .. }) => match lower.as_str() {
            "plus" | "minus" | "times" => Some(1),
            "divided" => Some(2),
            "whole" => Some(3),
            _ => None,
        },
        _ => None,
    }
}

// ---------- conditions ----------

fn parse_condition(
    toks: &[Token],
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    if toks.is_empty() {
        diags.push(diag(
            "T0124",
            "Question with nothing to check.",
            file,
            line,
            text,
            0,
            0,
            "Say if has no comparison.",
            "Compare it with something.",
        ));
        return;
    }
    let mut ts = TS::new(toks);
    if ts.peek_word() == Some("not") {
        ts.pos += 1;
    }
    parse_comparison(&mut ts, text, file, line, names, diags);
    let mut used_and = false;
    let mut used_or = false;
    while ts.pos < ts.toks.len() {
        if ts.peek_word() == Some("and") {
            used_and = true;
            ts.pos += 1;
            parse_comparison(&mut ts, text, file, line, names, diags);
        } else if ts.peek_word() == Some("or") {
            used_or = true;
            ts.pos += 1;
            parse_comparison(&mut ts, text, file, line, names, diags);
        } else {
            break;
        }
    }
    if used_and && used_or {
        diags.push(diag(
            "T0131",
            "A sentence cannot use both and and or. Split it into two sentences.",
            file,
            line,
            text,
            0,
            0,
            "One sentence uses both and and or.",
            "Split it into two sentences.",
        ));
    }
}

fn parse_comparison(
    ts: &mut TS,
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    // M4-G45 (Appendix K 7.5): `<file_ref> exists` is a yes-or-no question
    // without a comparison. The pre-scan only accepts the shape (the
    // reference words carry reserved steps of their own); the semantic
    // layer reads the file reference and checks its names.
    if ts.toks.len() >= 2 {
        if let Some(Token::Word { lower, .. }) = ts.toks.last() {
            if lower == "exists" {
                let lead = match ts.toks.first() {
                    Some(Token::Word { lower, .. }) => Some(lower.as_str()),
                    _ => None,
                };
                let single_word = ts.toks.len() == 2 && matches!(ts.toks[0], Token::Word { .. });
                if lead == Some("file") || lead == Some("folder") || single_word {
                    return;
                }
            }
        }
    }
    parse_operand(ts, text, file, line, names, diags);
    if ts.pos >= ts.toks.len() {
        diags.push(diag(
            "T0124",
            "Question with nothing to check.",
            file,
            line,
            text,
            0,
            0,
            "Say if has no comparison.",
            "Compare it with something.",
        ));
        return;
    }
    // `coll has x` (Ch.12) — no "is" word
    if ts.peek_word() == Some("has") {
        ts.pos += 1;
        parse_operand(ts, text, file, line, names, diags);
        return;
    }
    if ts.peek_word() != Some("is") {
        // Ch.8 wording: the operand that was not compared is named.
        let frag = ts.toks[..ts.pos]
            .iter()
            .filter_map(|t| match t {
                Token::Word { text, .. } => Some(text.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join(" ");
        let frag = if frag.is_empty() {
            "it".to_string()
        } else {
            frag
        };
        let what = format!(
            "A yes or no question needs something to check. Write what {frag} should be compared with."
        );
        diags.push(diag(
            "T0124",
            &what,
            file,
            line,
            text,
            0,
            0,
            "Say if has no comparison.",
            "Compare it with something.",
        ));
        return;
    }
    ts.pos += 1; // consume "is"
    // `coll is empty` / `coll [not] has x` / `x is missing` / `x is there` (Ch.11/12/18)
    if ts.peek_word() == Some("not") {
        ts.pos += 1;
    }
    match ts.peek_word() {
        Some("empty") => {
            ts.pos += 1;
            return;
        }
        Some("missing") | Some("there") => {
            ts.pos += 1;
            return;
        }
        Some("has") => {
            ts.pos += 1;
            parse_operand(ts, text, file, line, names, diags);
            return;
        }
        _ => {}
    }
    let mut is_between = false;
    match ts.peek_word() {
        Some("more") => {
            ts.pos += 1;
            if ts.peek_word() == Some("than") {
                ts.pos += 1;
            }
        }
        Some("less") => {
            ts.pos += 1;
            if ts.peek_word() == Some("than") {
                ts.pos += 1;
            }
        }
        Some("at") => {
            ts.pos += 1;
            if ts.peek_word() == Some("least") {
                ts.pos += 1;
            } else if ts.peek_word() == Some("most") {
                ts.pos += 1;
            }
        }
        Some("close") => {
            ts.pos += 1;
            if ts.peek_word() == Some("to") {
                ts.pos += 1;
            }
        }
        Some("between") => {
            ts.pos += 1;
            is_between = true;
        }
        _ => {}
    }
    // the value slot: a word immediately before a number is not a value the
    // pattern allows there (T0150: "If age is atleast 18 say adult.")
    if matches!(ts.peek(), Some(Token::Word { .. })) {
        let w = ts.peek_word().unwrap_or("").to_string();
        let num_after = matches!(
            ts.toks.get(ts.pos + 1),
            Some(Token::Whole { .. }) | Some(Token::Decimal { .. }) | Some(Token::Negative { .. })
        );
        if num_after && w != "minus" {
            diags.push(diag(
                "T0150",
                "Unknown word.",
                file,
                line,
                text,
                ts.pos,
                ts.pos + 1,
                "A word after the first word is not a word that the pattern allows at that place.",
                "Check the spelling of the word.",
            ));
            return;
        }
    }
    parse_operand(ts, text, file, line, names, diags);
    // only "between X and Y" takes a second value; the and must not be eaten
    // before parse_condition sees it (T0131 needs and/or in the outer loop)
    if is_between && ts.peek_word() == Some("and") {
        ts.pos += 1;
        parse_operand(ts, text, file, line, names, diags);
    }
}

// ---------- one-line statements ----------

fn parse_one_line_stmt(
    toks: &[Token],
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    in_loop: bool,
    diags: &mut Vec<Diagnostic>,
) {
    if toks.is_empty() {
        return;
    }
    let mut ts = TS::new(toks);
    match ts.peek_word() {
        Some("say") => {
            ts.pos += 1;
            parse_expr_tokens(&mut ts, text, file, line, names, diags);
        }
        Some("set") => {
            ts.pos += 1;
            let _ = ts.consume();
            if ts.peek_word() == Some("to") {
                ts.pos += 1;
            }
            parse_expr_tokens(&mut ts, text, file, line, names, diags);
        }
        Some("give") => {
            ts.pos += 1;
            if ts.peek_word() == Some("back") {
                ts.pos += 1;
            }
            if ts.peek_word().is_some() {
                parse_expr_tokens(&mut ts, text, file, line, names, diags);
            }
        }
        Some("stop") => {
            ts.pos += 1;
            if !in_loop {
                diags.push(diag(
                    "T0113",
                    "Stop outside a loop.",
                    file,
                    line,
                    text,
                    0,
                    4,
                    "Stop. is not inside a loop.",
                    "Use it inside Repeat or For each.",
                ));
            }
        }
        Some("skip") => {
            ts.pos += 1;
            if !in_loop {
                diags.push(diag(
                    "T0114",
                    "Skip outside a loop.",
                    file,
                    line,
                    text,
                    0,
                    4,
                    "Skip. is not inside a loop.",
                    "Use it inside Repeat or For each.",
                ));
            }
        }
        _ => {}
    }
}

fn parse_value_expr(
    words: &[&str],
    text: &str,
    file: &str,
    line: usize,
    _names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    if words.is_empty() {
        diags.push(diag(
            "T0107",
            "Definition without a value.",
            file,
            line,
            text,
            text.len(),
            text.len(),
            "is has nothing after it.",
            "Write the value after is.",
        ));
        return;
    }
    // Strip trailing period from last word
    let mut words: Vec<&str> = words.to_vec();
    if let Some(last) = words.last_mut() {
        *last = last.trim_end_matches('.');
    }
    // T0006 number spelled as letters (unless the value ends in "as text",
    // which makes the word a text value per Chapter 6)
    let first = words[0].to_ascii_lowercase();
    let has_as_text = words.len() >= 2
        && words[words.len() - 1].eq_ignore_ascii_case("text")
        && words[words.len() - 2].eq_ignore_ascii_case("as");
    if number_words().contains(&first.as_str()) && !has_as_text {
        diags.push(diag(
            "T0006",
            "Number spelled as letters.",
            file,
            line,
            text,
            0,
            words[0].len(),
            "A number is written as a word where a number is expected.",
            "Write the number with digits. To make the word a text value, write as text.",
        ));
        return;
    }
    // One operation per sentence (Ch.7): count the operations; a minus that
    // starts a value is a sign, never an operation.
    let mut ops = 0usize;
    let mut prev_operand = false;
    let mut i = 0;
    while i < words.len() {
        let w = words[i].to_ascii_lowercase();
        match w.as_str() {
            "plus" | "times" => {
                if prev_operand {
                    ops += 1;
                    prev_operand = false;
                }
            }
            "minus" => {
                if prev_operand {
                    ops += 1;
                    prev_operand = false;
                }
            }
            "divided" => {
                if prev_operand && i + 1 < words.len() && words[i + 1].eq_ignore_ascii_case("by") {
                    ops += 1;
                    prev_operand = false;
                    i += 1; // by
                }
            }
            "remainder" | "power" => {
                // remainder of A by B / power of A and B are single operations
                if i + 1 < words.len() && words[i + 1].eq_ignore_ascii_case("of") {
                    ops += 1;
                    prev_operand = false;
                    i += 1; // of
                }
            }
            "whole" => {
                // "whole divided by": the operation counts at divided
                if !(i + 1 < words.len() && words[i + 1].eq_ignore_ascii_case("divided")) {
                    prev_operand = true;
                }
            }
            _ => prev_operand = true,
        }
        i += 1;
    }
    if ops >= 2 {
        diags.push(diag(
            "T0109",
            "A sentence can hold one operation. Write each step on its own line.",
            file,
            line,
            text,
            0,
            text.len(),
            "A sentence chains two operations.",
            "Write each step in its own sentence.",
        ));
        return;
    }
}

// ---------- helpers ----------

fn number_words() -> &'static [&'static str] {
    &[
        "zero",
        "one",
        "two",
        "three",
        "four",
        "five",
        "six",
        "seven",
        "eight",
        "nine",
        "ten",
        "eleven",
        "twelve",
        "thirteen",
        "fourteen",
        "fifteen",
        "sixteen",
        "seventeen",
        "eighteen",
        "nineteen",
        "twenty",
        "thirty",
        "forty",
        "fifty",
        "sixty",
        "seventy",
        "eighty",
        "ninety",
        "hundred",
        "thousand",
        "million",
    ]
}

fn hard_word(w: &str) -> bool {
    hard_words().contains(&w.to_ascii_lowercase().as_str())
}

fn validate_word_name(
    original: &str,
    lower: &str,
    text: &str,
    file: &str,
    line: usize,
    _names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    let first = lower.split_whitespace().next().unwrap_or("");
    if hard_word(first) {
        diags.push(diag(
            "T0101",
            "Hard word in a name.",
            file,
            line,
            text,
            0,
            original.len(),
            "A word with a fixed meaning is used in a name.",
            "Choose another name.",
        ));
    } else if matches!(first, "macro" | "inherit" | "class" | "await") {
        diags.push(diag(
            "T0102",
            "Blocked future word.",
            file,
            line,
            text,
            0,
            original.len(),
            "A name is macro, inherit, class or await.",
            "Choose another name.",
        ));
    } else if matches!(first, "the" | "a" | "an") {
        diags.push(diag(
            "T0104",
            "Article used as a name.",
            file,
            line,
            text,
            0,
            original.len(),
            "A name is a, an or the, which are removed from code.",
            "Choose another name.",
        ));
    } else if original
        .chars()
        .next()
        .map_or(false, |ch| ch.is_ascii_digit())
    {
        diags.push(diag(
            "T0111",
            "Name starts with a digit.",
            file,
            line,
            text,
            0,
            original.len(),
            "A name begins with a digit.",
            "Begin the name with a letter.",
        ));
    }
}

fn validate_name(
    name: &str,
    text: &str,
    file: &str,
    line: usize,
    names: &NameTable,
    diags: &mut Vec<Diagnostic>,
) {
    // T0202 (S4): two names that differ only in the capital letters
    if names.case_clash(name, line) {
        let lo = text.find(name).unwrap_or(0);
        diags.push(diag(
            "T0202",
            "Names differ only in case.",
            file,
            line,
            text,
            lo,
            lo + name.len(),
            "Two names differ only in capital letters.",
            "Use one name.",
        ));
        return;
    }
    let first = name.split_whitespace().next().unwrap_or("");
    let first_lower = first.to_ascii_lowercase();
    if hard_word(first) {
        diags.push(diag(
            "T0101",
            "Hard word in a name.",
            file,
            line,
            text,
            0,
            name.len(),
            "A word with a fixed meaning is used in a name.",
            "Choose another name.",
        ));
    } else if matches!(
        first_lower.as_str(),
        "macro" | "inherit" | "class" | "await"
    ) {
        diags.push(diag(
            "T0102",
            "Blocked future word.",
            file,
            line,
            text,
            0,
            name.len(),
            "A name is macro, inherit, class or await.",
            "Choose another name.",
        ));
    } else if matches!(first_lower.as_str(), "the" | "a" | "an") {
        diags.push(diag(
            "T0104",
            "Article used as a name.",
            file,
            line,
            text,
            0,
            name.len(),
            "A name is a, an or the, which are removed from code.",
            "Choose another name.",
        ));
    } else if name.chars().next().map_or(false, |ch| ch.is_ascii_digit()) {
        diags.push(diag(
            "T0106",
            "Definition without is.",
            file,
            line,
            text,
            0,
            name.len(),
            "A sentence begins with a name but has no is.",
            "Write Name is value.",
        ));
    }
}

/// A cursor over a token slice.
struct TS<'a> {
    toks: &'a [Token],
    pos: usize,
}

impl<'a> TS<'a> {
    fn new(toks: &'a [Token]) -> Self {
        Self { toks, pos: 0 }
    }
    fn peek(&self) -> Option<&Token> {
        self.toks.get(self.pos)
    }
    fn peek_word(&self) -> Option<&str> {
        self.toks.get(self.pos).and_then(|t| match t {
            Token::Word { lower, .. } => Some(lower.as_str()),
            _ => None,
        })
    }
    fn consume(&mut self) -> Option<Token> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
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
