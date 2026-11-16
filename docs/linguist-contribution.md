# Getting GitHub to show "Lykaon %" in the Languages bar

GitHub's language detector ([github/linguist](https://github.com/github/linguist))
only knows a fixed list of languages. `.lykaon` is not on that list yet, so
`.lykaon` files count as *nothing* and the bar shows mostly Rust (the compiler
source). This is normal for a brand-new language — Python and Rust got on the
list the same way: someone sent a pull request.

This folder contains everything ready to submit that pull request. It takes
about 15 minutes, no special access, and it benefits every repository that
uses `.lykaon` — not just this one.

## Step 1 — Fork github/linguist and add the language

Edit [`lib/linguist/languages.yml`](https://github.com/github/linguist/blob/main/lib/linguist/languages.yml)
and append an entry like this (keep alphabetical order — Lykaon goes near Lua):

```yaml
Lykaon:
  type: programming
  color: "#5b8def"
  extensions:
    - ".lykaon"
  tm_scope: source.lykaon
  ace_mode: text
  language_id: 0
```

Notes:

- `language_id` must be a unique number; check the file for the current
  highest id and use the next free one (the maintainers will confirm it).
- `color` is the bar color; pick any hex you like.
- `tm_scope: source.lykaon` is what TextMate grammars register under later.

## Step 2 — Add a sample file

Create `samples/Lykaon/hello.lykaon` in the linguist repo, with content like:

```lykaon
Note Lykaon sample for linguist language detection.
About a small program that says hello and does a little math.

Changeable count is 3.
Repeat while count is at least 1.
    Say hello from Lykaon number count.
    Set count to count minus 1.

Total is 4.
Changeable x is 2.
Set x to x times Total.
Say x.

Numbers is list of 5 and 2 and 8.
For each n in Numbers.
    Say n plus 1.
```

(Keep it short and representative — linguist uses samples for detection tests.)

## Step 3 — Send the pull request

Open a PR titled something like **"Add Lykaon language"** with:

- a link to this repository (https://github.com/Lykaon-oss/Lykaon) as the
  language's home page,
- a short description: *Lykaon is a programming language written in plain
  English sentences; programs end in `.lykaon`; see the linked repo for the
  compiler, tests and documentation.*

The maintainers may ask for proof that the language is real and used — point
them at this repo, its test suite and the working `lykaonc-cli build`.

## Step 4 — After the PR merges

Add the enabled line to `.gitattributes` in this repository (it is already
prepared, commented out at the bottom of the file):

```gitattributes
*.lykaon linguist-language=Lykaon
```

From the next re-index, GitHub shows **Lykaon** with its percentage in the
Languages bar of every repository that contains `.lykaon` files.

## Why the bar shows Rust today

The compiler, interpreter and runtime are written in Rust, so even before
`.lykaon` is recognized, Rust will dominate the percentages. That is honest:
the *implementation* is Rust; the *language users write* is Lykaon. Once the
linguist PR merges, both show: Lykaon for the `.lykaon` sources and tests,
Rust for the compiler.
