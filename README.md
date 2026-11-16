# Lykaon

**Lykaon** is a programming language where you write programs in plain English sentences.
A sentence ends with a period. A block is indented. There are no quotes, no braces,
no semicolons. The compiler reads your sentences and builds a real native executable.

This repository holds Lykaon **version 0.1 (milestones M1–M4)**: the language core,
the interpreter, the native compiler, the runtime library, and the conformance test
suite that defines what the language must do.

```lykaon
Say hello world from Lykaon today.
```

```
> lykaonc-cli build fast hello.lykaon hello.exe
built hello in fast
> hello.exe
hello world from Lykaon today
```

## What is inside version 0.1

| Area | What you get |
|---|---|
| M1 — Language core | Sentences, blocks, `Changeable`/`Constant`/`Set`, `Say`, `Ask`, `If`/`Otherwise`, `Repeat`, `For each`, math and comparison words, a formatter, and precise error messages (`Where`/`Why`/`Fix`) |
| M2 — Data and ownership | Lists, maps, sets, pairs, text in depth, records, enums, `maybe`/`missing`, `can fail`/`Try`/`Fail with`, modules (`Use`, `Share`), tests (`Test`, `Check`, `Pretend`), ownership (`give`, `lend`, `copy of`, `share`, `weak`) |
| M3 — Native code | The Cranelift-backed compiler: `lykaon build` in debug/fast/small modes, an optimizer (inlining, dead-code removal, bounds-check elimination, devirtualization, whole-program passes), generics, interfaces, closures, generators, contracts (`Requires`, `Ensures`, `Always`), packages (`Lykaon.toml`, `lykaon.lock`, `lykaon add/remove/update`), `lykaon bench` |
| M4 — Servers and concurrency | Tasks (`Start task`, `Wait for`, `Do these together`), channels, guarded/atomic/counter values, timers (`After`, `Every`), worker pools, files and folders, zip/gzip, JSON/TOML/YAML/XML/CSV read and write, dates and time zones, random, hashing, secrets, `Run`/`Exit`/signals, logging and settings, HTTP client and server with TLS, templates, sessions and WebSocket, command-line tools (`Takes`, `Option`, help text), git dependencies |

In v0.1 a `.lykaon` program builds to a **command-line / console executable** on Windows
(proven by the test suite) and Linux (in principle; not yet verified on Linux hardware —
see *Known limits*). Desktop/windowed apps arrive in a later version.

## Try it

Build from source (you need [Rust](https://rustup.rs) 1.75 or newer):

```
cargo build --release
```

The interpreter:

```
lykaon-cli run examples\hello.lykaon
lykaon-cli repl
```

The compiler:

```
lykaonc-cli build fast hello.lykaon hello.exe
hello.exe
```

Run the test suite:

```
cargo test
```

## Documentation

| File | Contents |
|---|---|
| [`docs/syntax.md`](docs/syntax.md) | The 5-minute tour: variables, control flow, functions, modules |
| [`docs/standard-library.md`](docs/standard-library.md) | The built-in words, grouped by task |
| [`docs/cli.md`](docs/cli.md) | Every command: run, repl, build, test, add, update, bench |
| [`docs/Lykaon_Language_Reference.docx`](docs/Lykaon_Language_Reference.docx) | The complete language reference for v0.1 (M1–M4), in one document |

## Repository layout

```
Lykaon/            the language workspace
  core/            lexer, parser, interpreter, MIR, codegen, net, formats
  rt/              lykaon-rt, the runtime library linked into built programs
  src/             the two front ends (lykaon-cli, lykaonc-cli), linker, packages
  tests/           conformance tests, benchmarks, ownership suite
LICENSES/          third-party license texts
logos/             project logos
```

## Status and limits (read this before you rely on it)

- **Windows**: everything above is tested and passing on Windows x86-64.
- **Linux**: the compiler cross-builds a static Linux executable and runtime, but the
  test suite has not yet been executed on Linux. Treat Linux as unverified in v0.1.
- **Performance**: roughly 67–72% of equivalent Rust speed on the six standard
  benchmarks. Faster backends are planned for later versions.
- **Windowed apps**: not in v0.1. Only command-line and console programs.

## License

Lykaon is **source-available, not open source**. It is free for personal use and for
organizations under USD 1,000,000 annual revenue; see [`LICENSE.md`](LICENSE.md) for
the exact terms. Third-party components are listed in [`THIRD_PARTY.json`](THIRD_PARTY.json)
and [`LICENSES/`](LICENSES/).

Programs you write in Lykaon are **yours** — you may license and sell them freely.
