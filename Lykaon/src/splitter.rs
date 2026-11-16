//! Sentence splitter: one sentence per line, indented blocks (Ch.3, p.20).
//! Produces lexing diagnostics (T0001-T0024).

use crate::diagnostics::Diagnostic;

const MAX_LINE_LEN: usize = 200;

#[derive(Clone, Debug)]
pub struct Sentence {
    pub line: usize,          // 1-based
    pub indent: usize,        // indent level (number of 4-space indents)
    pub text: String,         // line content without leading indentation
    pub children: Vec<usize>, // indices into the flat all vec
    pub is_raw_text: bool,    // true for lines under "Say lines."
}

#[derive(Clone, Debug)]
pub struct SplitResult {
    pub all: Vec<Sentence>, // flat list of all sentences, in order
    pub roots: Vec<usize>,  // indices into `all` for root-level sentences
    pub diagnostics: Vec<Diagnostic>,
}

fn err(
    code: &'static str,
    what: String,
    file: &str,
    line: usize,
    sentence: String,
    lo: usize,
    hi: usize,
    why: String,
    fix: String,
) -> Diagnostic {
    Diagnostic::error(
        code,
        what,
        file.to_string(),
        line,
        sentence,
        lo,
        hi,
        why,
        fix,
    )
}

fn warn(
    code: &'static str,
    what: String,
    file: &str,
    line: usize,
    sentence: String,
    lo: usize,
    hi: usize,
    why: String,
    fix: String,
) -> Diagnostic {
    Diagnostic::warning(
        code,
        what,
        file.to_string(),
        line,
        sentence,
        lo,
        hi,
        why,
        fix,
    )
}

/// Split source into sentences. Returns sentences plus any lexing diagnostics.
pub fn split_source(source: &str, file_name: &str) -> Result<SplitResult, Vec<Diagnostic>> {
    let mut diags: Vec<Diagnostic> = Vec::new();

    // UTF-8 validation (T0018). BOM at start ignored.
    let bytes = source.as_bytes();
    let start = if bytes.len() >= 3 && bytes[0] == 0xEF && bytes[1] == 0xBB && bytes[2] == 0xBF {
        3
    } else {
        0
    };
    if std::str::from_utf8(&bytes[start..]).is_err() {
        return Err(vec![err(
            "T0018",
            "The file is not UTF-8.".to_string(),
            file_name,
            1,
            source.lines().next().unwrap_or("").to_string(),
            0,
            0,
            "The file holds bytes that are not valid UTF-8.".to_string(),
            "Save the file as UTF-8.".to_string(),
        )]);
    }

    // Normalize CRLF and lone CR to LF; track mixed endings (T0024 warning).
    let has_cr = bytes[start..].contains(&b'\r');
    let has_lf = bytes[start..].contains(&b'\n');
    let text = &source[start..];
    let normalized = text.replace("\r\n", "\n").replace('\r', "\n");
    if has_cr && has_lf {
        let first = normalized.lines().next().unwrap_or("");
        diags.push(warn(
            "T0024",
            "Mixed line endings.".to_string(),
            file_name,
            1,
            first.to_string(),
            0,
            0,
            "The file uses both LF and CRLF.".to_string(),
            "Run lykaon fmt.".to_string(),
        ));
    }

    let lines: Vec<&str> = normalized.split('\n').collect();

    // Per-line analysis.
    let mut infos: Vec<LineInfo> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let line_no = i + 1;
        let leading = line.chars().take_while(|c| *c == ' ').count();
        let content = line[leading..].trim_end();
        let tab_pos = line.find('\t');
        let odd = leading > 0 && leading % 4 != 0;
        let long = line.len() > MAX_LINE_LEN;
        let trailing = line.len() != line.trim_end().len();
        infos.push(LineInfo {
            line_no,
            line: line.to_string(),
            leading,
            indent: leading / 4,
            content: content.to_string(),
            tab_pos,
            odd,
            long,
            trailing,
        });
    }

    // T0001 tab (report first)
    if let Some(info) = infos.iter().find(|i| i.tab_pos.is_some()) {
        let p = info.tab_pos.unwrap();
        diags.push(err(
            "T0001",
            "A tab is not allowed. Use 4 spaces.".to_string(),
            file_name,
            info.line_no,
            info.line.clone(),
            p,
            p + 1,
            "A line is indented with a tab character.".to_string(),
            "Use 4 spaces for each level.".to_string(),
        ));
    }
    // T0002 odd indentation (report first, only if no T0001)
    if diags.iter().all(|d| d.code != "T0001") {
        if let Some(info) = infos.iter().find(|i| i.odd) {
            diags.push(err(
                "T0002",
                "Odd indentation.".to_string(),
                file_name,
                info.line_no,
                info.line.clone(),
                0,
                info.leading,
                "Indentation is not a multiple of 4 spaces.".to_string(),
                "Indent by exactly 4 spaces per level.".to_string(),
            ));
        }
    }
    // T0003 line too long (all)
    for info in &infos {
        if info.long {
            diags.push(err(
                "T0003",
                "Line too long.".to_string(),
                file_name,
                info.line_no,
                info.line.clone(),
                0,
                info.line.len(),
                "A line holds more than 200 characters.".to_string(),
                "Split the idea into shorter sentences.".to_string(),
            ));
        }
    }
    // T0013 empty sentence (a line holding only a period)
    for info in &infos {
        if info.content == "." {
            diags.push(err(
                "T0013",
                "Empty sentence.".to_string(),
                file_name,
                info.line_no,
                info.line.clone(),
                0,
                1,
                "A line holds only a period.".to_string(),
                "Remove the line.".to_string(),
            ));
        }
    }
    // T0004 nesting too deep (more than 32 levels)
    for info in &infos {
        if info.indent > 32 {
            diags.push(err(
                "T0004",
                "Nesting too deep.".to_string(),
                file_name,
                info.line_no,
                info.line.clone(),
                0,
                info.leading,
                "Blocks are nested deeper than 32 levels.".to_string(),
                "Move inner blocks into functions.".to_string(),
            ));
        }
    }
    // T0021 trailing spaces (all)
    for info in &infos {
        if info.trailing {
            let te = info.line.trim_end().len();
            diags.push(warn(
                "T0021",
                "Trailing spaces.".to_string(),
                file_name,
                info.line_no,
                info.line.clone(),
                te,
                info.line.len(),
                "A line ends with spaces.".to_string(),
                "Run lykaon fmt.".to_string(),
            ));
        }
    }

    // Build the indentation tree and check indentation rules.
    let mut roots: Vec<usize> = Vec::new();
    // last line index at each indent level (indices into a flat vec of all non-blank sentences in order)
    let mut last_at_level: Vec<Option<usize>> = Vec::new();
    let mut all: Vec<Sentence> = Vec::new(); // flat list, in order, to link children

    for info in &infos {
        if info.content.is_empty() {
            continue; // blank lines ignored here (T0020 handled below)
        }
        // T0023 extra spaces between words
        if let Some(p) = info.content.find("  ") {
            diags.push(warn(
                "T0023",
                "Extra spaces.".to_string(),
                file_name,
                info.line_no,
                info.content.clone(),
                p,
                p + 2,
                "More than one space between words outside raw text.".to_string(),
                "Run lykaon fmt.".to_string(),
            ));
        }

        let indent = info.indent;
        while last_at_level.len() <= indent {
            last_at_level.push(None);
        }
        let idx = all.len();
        let sentence = Sentence {
            line: info.line_no,
            indent,
            text: info.content.clone(),
            children: Vec::new(),
            is_raw_text: false,
        };
        all.push(sentence);

        if indent == 0 {
            roots.push(idx);
        } else {
            // parent must be the last line at indent-1 and must open a block
            let parent_idx = last_at_level[indent - 1];
            match parent_idx {
                Some(p) if can_open_block(&all[p].text) => {
                    all[p].children.push(idx);
                }
                _ => {
                    // T0015 unexpected indent
                    let mark = " ".repeat(indent * 4);
                    diags.push(err(
                        "T0015",
                        "Unexpected indent.".to_string(),
                        file_name,
                        info.line_no,
                        info.content.clone(),
                        0,
                        mark.len(),
                        "A line is indented but no sentence above opens a block.".to_string(),
                        "Remove the indentation.".to_string(),
                    ));
                }
            }
        }
        last_at_level[indent] = Some(idx);
        // clear deeper levels
        for l in (indent + 1)..last_at_level.len() {
            last_at_level[l] = None;
        }
    }

    // Mark lines under "Say lines." as raw text (not sentences).
    mark_raw_text(&mut all, &roots);

    // T0005 stray period (checked on the sentences, after the marking)
    check_stray_period(&all, &roots, file_name, &mut diags);

    // T0022 sentence starts lower case (raw text is never changed).
    check_t0022(&all, &roots, file_name, &mut diags);

    // T0014 block opener without a block (recursively)
    check_block_openers(&all, &roots, file_name, &mut diags);

    // T0020 extra blank lines (more than one in a row)
    let mut blank_run = 0usize;
    for info in &infos {
        if info.content.is_empty() {
            blank_run += 1;
            if blank_run > 1 {
                diags.push(warn(
                    "T0020",
                    "Extra blank lines.".to_string(),
                    file_name,
                    info.line_no,
                    info.line.clone(),
                    0,
                    0,
                    "More than one blank line in a row.".to_string(),
                    "Run lykaon fmt.".to_string(),
                ));
            }
        } else {
            blank_run = 0;
        }
    }

    Ok(SplitResult {
        all,
        roots,
        diagnostics: diags,
    })
}

fn check_block_openers(
    all: &[Sentence],
    roots: &[usize],
    file_name: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for &idx in roots {
        let s = &all[idx];
        let is_opener = is_block_opener(&s.text);
        // A one-line `Try <sentence>.` is legal (the block is optional), so a
        // `try` line without indented children is not a block opener error;
        // the type layer reports T0151 when the tried sentence cannot fail.
        let is_try = s
            .text
            .split_whitespace()
            .next()
            .map_or(false, |w| w.eq_ignore_ascii_case("try"));
        if is_opener && s.children.is_empty() && !is_try {
            diags.push(err(
                "T0014",
                "Block opener without a block.".to_string(),
                file_name,
                s.line,
                s.text.clone(),
                s.text.len(),
                s.text.len(),
                "A line ends with a period like an opener, and nothing is indented under it."
                    .to_string(),
                "Indent the sentences that belong under it.".to_string(),
            ));
        }
        check_block_openers(all, &s.children, file_name, diags);
    }
}

/// Mark children of "Say lines." sentences as raw text.
fn mark_raw_text(all: &mut [Sentence], roots: &[usize]) {
    for &idx in roots {
        let is_say_lines = {
            let s = &all[idx];
            let mut w = s.text.split_whitespace();
            w.next().map_or(false, |fw| fw.eq_ignore_ascii_case("say"))
                && w.next().map_or(false, |sw| {
                    sw.trim_end_matches('.').eq_ignore_ascii_case("lines")
                })
        };
        if is_say_lines {
            let children: Vec<usize> = {
                let s = &all[idx];
                s.children.clone()
            };
            for &child_idx in &children {
                all[child_idx].is_raw_text = true;
            }
        }
        let children: Vec<usize> = {
            let s = &all[idx];
            s.children.clone()
        };
        mark_raw_text(all, &children);
    }
}

/// T0005 stray period (a period neither at the end of the line nor
/// between two digits), skipping raw text and the text-taking words.
/// The period must be followed by a space and a word (two sentences on
/// one line); a dot inside a word (`m48sayhi.exe`) is the Run name's
// own T0113 shape.
fn check_stray_period(
    all: &[Sentence],
    roots: &[usize],
    file_name: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for &idx in roots {
        let s = &all[idx];
        if s.is_raw_text {
            continue;
        }
        let first = s.text.split_whitespace().next().unwrap_or("");
        if first.eq_ignore_ascii_case("note") || first.eq_ignore_ascii_case("about") {
            continue; // the text is raw (ch.3)
        }
        let content = s.text.trim_end_matches('.');
        if content.len() == s.text.len() {
            continue; // the sentence ends with its period
        }
        // a period inside the line, not between two digits, followed by
        // a space and a word (two sentences on one line)
        for (p, c) in content.char_indices() {
            if c != '.' {
                continue;
            }
            let rest = &content[p + 1..];
            let two_sentences = rest.starts_with(' ')
                && rest
                    .trim_start()
                    .chars()
                    .next()
                    .map_or(false, |d| d.is_alphabetic());
            if two_sentences {
                diags.push(err(
                    "T0005",
                    "Stray period.".to_string(),
                    file_name,
                    s.line,
                    s.text.clone(),
                    p,
                    p + 1,
                    "A period is neither at the end of a line nor between two digits.".to_string(),
                    "Write one sentence on each line.".to_string(),
                ));
                break;
            }
        }
        check_stray_period_children(all, &s.children, file_name, diags);
    }
}

fn check_stray_period_children(
    all: &[Sentence],
    indices: &[usize],
    file_name: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for &idx in indices {
        let s = &all[idx];
        if !s.is_raw_text {
            let first = s.text.split_whitespace().next().unwrap_or("");
            if !first.eq_ignore_ascii_case("note") && !first.eq_ignore_ascii_case("about") {
                let content = s.text.trim_end_matches('.');
                if content.len() != s.text.len() {
                    for (p, c) in content.char_indices() {
                        if c != '.' {
                            continue;
                        }
                        let rest = &content[p + 1..];
                        let two_sentences = rest.starts_with(' ')
                            && rest
                                .trim_start()
                                .chars()
                                .next()
                                .map_or(false, |d| d.is_alphabetic());
                        if two_sentences {
                            diags.push(err(
                                "T0005",
                                "Stray period.".to_string(),
                                file_name,
                                s.line,
                                s.text.clone(),
                                p,
                                p + 1,
                                "A period is neither at the end of a line nor between two digits."
                                    .to_string(),
                                "Write one sentence on each line.".to_string(),
                            ));
                            break;
                        }
                    }
                }
            }
        }
        check_stray_period_children(all, &s.children, file_name, diags);
    }
}

/// Check T0022 (sentence starts lower case), skipping raw text lines.
fn check_t0022(all: &[Sentence], roots: &[usize], file_name: &str, diags: &mut Vec<Diagnostic>) {
    for &idx in roots {
        let s = &all[idx];
        if !s.is_raw_text {
            if let Some(first) = s.text.chars().next() {
                if first.is_ascii_lowercase() {
                    diags.push(warn(
                        "T0022",
                        "Sentence starts in lower case.".to_string(),
                        file_name,
                        s.line,
                        s.text.clone(),
                        0,
                        first.len_utf8(),
                        "A sentence starts with a small letter.".to_string(),
                        "Run lykaon fmt.".to_string(),
                    ));
                }
            }
        }
        check_t0022(all, &s.children, file_name, diags);
    }
}

struct LineInfo {
    line_no: usize,
    line: String,
    leading: usize,
    indent: usize,
    content: String,
    tab_pos: Option<usize>,
    odd: bool,
    long: bool,
    trailing: bool,
}

/// A sentence that can open an indented block.
/// A line that ends with a period and opens a block (used for T0014).
/// Returns true only for actual block openers, not one-line forms.
fn is_block_opener(text: &str) -> bool {
    let trimmed = text.trim_end();
    if !trimmed.ends_with('.') {
        return false;
    }
    let mut words = trimmed.split_whitespace();
    let first = words
        .next()
        .unwrap_or("")
        .trim_end_matches('.')
        .to_ascii_lowercase();
    match first.as_str() {
        "if" => {
            // "If that fails use X." is a plain sentence, not an opener.
            // A one-line question ("If age is not 20 say different.",
            // "If n is 0 give back 0.") is also not an opener.
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            if ws.len() >= 3
                && ws[1].trim_end_matches('.').eq_ignore_ascii_case("that")
                && ws[2].trim_end_matches('.').eq_ignore_ascii_case("fails")
            {
                return false;
            }
            !has_one_line_action(&ws)
        }
        "otherwise" => {
            // "Otherwise." opens a block; "Otherwise say equal." does not.
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            !has_one_line_action(&ws)
        }
        "try" | "look" | "careful" | "together" | "start" | "test" => true,
        // M4-10: "Serve ..." opens its block (S64: it holds the When
        // someone blocks and the ordinary sentences); "Be careful." is
        // the two-word opener of the careful block (S62)
        "serve" => true,
        "be" => {
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            ws.len() == 2 && ws[1].trim_end_matches('.').eq_ignore_ascii_case("careful")
        }
        "do" => {
            // M4 (Appendix K): only "Do these together." opens a block;
            // other sentences that begin with do are ordinary one-liners.
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            ws.len() >= 3
                && ws[1].trim_end_matches('.').eq_ignore_ascii_case("these")
                && ws[2].trim_end_matches('.').eq_ignore_ascii_case("together")
        }
        "check" => {
            // "Check that this fails." and "Check for any ..." open blocks
            // (ch.38); other checks are one-line asserts.
            let low = trimmed.to_ascii_lowercase();
            low.contains("this fails") || low.starts_with("check for any")
        }
        "repeat" => {
            // Block opener only if "Repeat N times.", "Repeat forever." or
            // "Repeat while <cond>." (no stmt after and no one-line stmt)
            let second = words.next().unwrap_or("").trim_end_matches('.');
            let third = words.next().unwrap_or("").trim_end_matches('.');
            let fourth = words.next().unwrap_or("").trim_end_matches('.');
            // "repeat <number> times." -> block. "repeat forever." -> block.
            // "repeat <number> times <stmt>." -> one-line, not block.
            (second.chars().all(|c| c.is_ascii_digit()) && third == "times" && fourth.is_empty())
                || (second == "forever" && third.is_empty())
                || (second == "while" && fourth.is_empty())
        }
        "to" => {
            // A one-line function ("To double n give n times 2.") is not a block
            // opener; a block function ("To classify n.") needs an indented body.
            !to_has_inline_give(&trimmed)
        }
        "for" => {
            // "For each x from A to B." with a block.
            let second = words.next().unwrap_or("").trim_end_matches('.');
            let _third = words.next().unwrap_or("").trim_end_matches('.');
            second == "each" && (third_is_loop_var(&trimmed))
        }
        // M4-4 (Appendix K 7.3/7.4): the timer and spread sentences own
        // indented blocks.
        "after" | "every" => {
            // "After 5 seconds." / "Every 5 seconds." (number, unit, end)
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            ws.len() == 3
                && ws[1].chars().all(|c| c.is_ascii_digit())
                && [
                    "milliseconds",
                    "seconds",
                    "minutes",
                    "hours",
                    "days",
                    "weeks",
                ]
                .iter()
                .any(|u| ws[2].trim_end_matches('.').eq_ignore_ascii_case(u))
        }
        "spread" => {
            // "Spread each of <items> over workers." - the block is required
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            ws.len() >= 5
                && ws[1].trim_end_matches('.').eq_ignore_ascii_case("each")
                && ws[2].trim_end_matches('.').eq_ignore_ascii_case("of")
                && ws[ws.len() - 2]
                    .trim_end_matches('.')
                    .eq_ignore_ascii_case("over")
                && ws[ws.len() - 1]
                    .trim_end_matches('.')
                    .eq_ignore_ascii_case("workers")
        }
        "say" => {
            // "Say lines." is a block opener (raw text children)
            let second = words.next().unwrap_or("").trim_end_matches('.');
            let third = words.next().unwrap_or("").trim_end_matches('.');
            second == "lines" && third.is_empty()
        }
        "about" => {
            let second = words.next().unwrap_or("").trim_end_matches('.');
            second.is_empty()
        }
        // M3 (ch.23): "A dog can speak." opens the impl block that holds its
        // To sentences. "A dog has ... ." with Always children is handled by
        // can_open_block; it is not a required opener.
        "a" | "an" => {
            let ws: Vec<&str> = trimmed.split_whitespace().collect();
            ws.windows(2)
                .any(|w| w[0].eq_ignore_ascii_case("can") && !w[1].trim_end_matches('.').is_empty())
        }
        _ => false,
    }
}

/// True when a "To ..." line is a one-line function: the word give appears on
/// the line (after the name and inputs), so no indented body is expected.
fn to_has_inline_give(text: &str) -> bool {
    let words: Vec<&str> = text.split_whitespace().collect();
    // Skip the To, the name and its inputs; "give" marks the one-line form.
    // "block": [_to, name, (input), (with input)...] then optional "give x".
    // block simple: "give" appears after the first input.
    // "with" separates further inputs, so the give (if any) is the last cluster;
    // easiest: any "give" that is not the word "gives"…
    // "to double n give n times 2." -> give at position 3.
    // A block function never has give on the To line.
    words
        .iter()
        .skip(2)
        .any(|w| w.trim_end_matches('.').eq_ignore_ascii_case("give"))
}

/// Words that make an If/Otherwise sentence a one-line form: the action's
/// sentence follows on the same line (G20). Whole-word match only.
fn has_one_line_action(ws: &[&str]) -> bool {
    ws.iter().skip(1).any(|w| {
        matches!(
            w.trim_end_matches('.').to_ascii_lowercase().as_str(),
            "say"
                | "set"
                | "give"
                | "stop"
                | "skip"
                | "fail"
                | "hand"
                | "add"
                | "remove"
                | "put"
                | "send"
        )
    })
}

/// True when the tokens after "For each" are loop header words
/// (from A to B, or in name).
fn third_is_loop_var(text: &str) -> bool {
    // "for each <var> from A to B." / "for each <x> in <list>."
    words_after_each_open_block(text)
}

fn words_after_each_open_block(text: &str) -> bool {
    let words: Vec<&str> = text.split_whitespace().collect();
    if words.len() < 4 {
        return false;
    }
    let w3 = words[3].trim_end_matches('.').to_ascii_lowercase();
    if w3 == "as" {
        // M4-G16 (Appendix K 7.4): For each x as they arrive from CH.
        let w4 = words
            .get(4)
            .map(|w| w.trim_end_matches('.').to_ascii_lowercase());
        let w5 = words
            .get(5)
            .map(|w| w.trim_end_matches('.').to_ascii_lowercase());
        let w6 = words
            .get(6)
            .map(|w| w.trim_end_matches('.').to_ascii_lowercase());
        return w4.as_deref() == Some("they")
            && w5.as_deref() == Some("arrive")
            && w6.as_deref() == Some("from");
    }
    w3 == "from" || w3 == "in"
}

fn can_open_block(text: &str) -> bool {
    let first = text
        .split_whitespace()
        .next()
        .unwrap_or("")
        .trim_end_matches('.')
        .to_ascii_lowercase();
    match first.as_str() {
        "if" | "otherwise" | "repeat" | "for" | "try" | "look"
        | "careful" | "together" | "start" | "test" | "about" | "to"
        // a When block of a Look at holds its body (ch.21)
        | "when" => true,
        // M4-10: Serve opens its block; Be careful. is a two-word opener
        "serve" => true,
        "be" => {
            let ws: Vec<&str> = text.split_whitespace().collect();
            ws.len() == 2 && ws[1].trim_end_matches('.').eq_ignore_ascii_case("careful")
        }
        // M3 (ch.23/64): a record sentence may hold an indented Always block;
        // an impl sentence "A dog can speak." holds its To sentences.
        "a" | "an" => true,
        // "Check that this fails." and "Check for any ..." open blocks (ch.38)
        "check" => {
            let low = text.to_ascii_lowercase();
            low.contains("this fails") || low.starts_with("check for any")
        }
        "say" => {
            let second = text.split_whitespace().nth(1).unwrap_or("").trim_end_matches('.');
            second.eq_ignore_ascii_case("lines")
        }
        // M4 (Appendix K): only "Do these together." opens a block.
        "do" => {
            let ws: Vec<&str> = text.split_whitespace().collect();
            ws.len() >= 3
                && ws[1].trim_end_matches('.').eq_ignore_ascii_case("these")
                && ws[2].trim_end_matches('.').eq_ignore_ascii_case("together")
        }
        // M4-4 (Appendix K 7.3/7.4): the timer, stream and spread lines can
        // hold indented bodies (the semantic layer reports wrong shapes).
        "after" | "every" | "spread" => true,
        _ => false,
    }
}
