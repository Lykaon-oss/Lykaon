//! Name pre-scan: find every defined name before parsing (Ch.4, p.22; Ch.65, p.166).
//! Collects names by spelling only; no kinds or values.

use crate::splitter::Sentence;

/// All names defined in the file, keyed by lowercase spelling.
#[derive(Clone, Debug, Default)]
pub struct NameTable {
    /// (lowercase name, original spelling, defining line)
    pub names: Vec<(String, String, usize)>,
}

impl NameTable {
    pub fn contains(&self, spelling: &str) -> bool {
        self.names.iter().any(|(n, _, _)| n == spelling)
    }
    /// All defined names as lowercase strings (for longest-first matching).
    pub fn spellings(&self) -> Vec<String> {
        self.names.iter().map(|(n, _, _)| n.clone()).collect()
    }
    /// T0202 (S4): a defined name that differs from `spelling` only in
    /// the capital letters, from an earlier line.
    pub fn case_clash(&self, spelling: &str, line: usize) -> bool {
        let lower = spelling.to_ascii_lowercase();
        self.names
            .iter()
            .any(|(n, orig, def_line)| *n == lower && *def_line < line && *orig != spelling)
    }
}

/// Collect every defined name by spelling: names left of `is`, after Changeable,
/// Constant and Ask, and (for later milestones) function inputs.
pub fn collect_names(all: &[Sentence], roots: &[usize]) -> NameTable {
    let mut names = Vec::new();
    collect_block(all, roots, &mut names);
    NameTable { names }
}

fn collect_block(all: &[Sentence], indices: &[usize], names: &mut Vec<(String, String, usize)>) {
    for &idx in indices {
        let s = &all[idx];
        let first = first_word(&s.text);
        match first.as_str() {
            "changeable" => {
                // Changeable <name> is ...
                if let Some(n) = second_word(&s.text) {
                    names.push((n.to_ascii_lowercase(), n, s.line));
                }
            }
            "constant" => {
                if let Some(n) = second_word(&s.text) {
                    names.push((n.to_ascii_lowercase(), n, s.line));
                }
            }
            "ask" => {
                // Ask <name> [as type].
                if let Some(n) = second_word(&s.text) {
                    names.push((n.to_ascii_lowercase(), n, s.line));
                }
            }
            _ => {
                // <name> is ...  (define)  -- first word is a name, second word is "is"
                let words: Vec<&str> = s.text.split_whitespace().collect();
                if words.len() >= 2 && words.iter().any(|w| w.eq_ignore_ascii_case("is")) {
                    // name may be multiple words: everything before "is"
                    let name_end = words
                        .iter()
                        .position(|w| w.eq_ignore_ascii_case("is"))
                        .unwrap_or(1);
                    // the articles the/a/an are removed from code before
                    // Tern reads it (ch.4): `The words is ...` defines
                    // `words`
                    let start =
                        words
                            .first()
                            .map_or(0, |w| match w.to_ascii_lowercase().as_str() {
                                "the" | "a" | "an" => 1,
                                _ => 0,
                            });
                    if name_end > start {
                        let name = words[start..name_end].join(" ");
                        if !name.is_empty() {
                            names.push((name.to_ascii_lowercase(), name, s.line));
                        }
                    } else if name_end == 1 {
                        // `The is 5.` - the article alone: T0103's shape
                        names.push((String::new(), String::new(), s.line));
                    }
                }
            }
        }
        collect_block(all, &s.children, names);
    }
}

fn first_word(text: &str) -> String {
    text.split_whitespace()
        .next()
        .unwrap_or("")
        .trim_end_matches('.')
        .to_ascii_lowercase()
}

fn second_word(text: &str) -> Option<String> {
    let mut words = text.split_whitespace();
    words.next(); // skip first
    words.next().map(|w| w.to_string())
}
