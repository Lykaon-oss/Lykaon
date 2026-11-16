# The Lykaon command line (v0.1)

Two programs come with a release:

| Program | Role |
|---|---|
| `lykaon-cli.exe` (`lykaon`) | the interpreter front end: run, repl, ui, package commands |
| `lykaonc-cli.exe` (`lykaonc`) | the compiler front end: build native executables |

## Running programs

```
lykaon-cli run program.lykaon          run a program
lykaon-cli run --native program.lykaon run through the native path
lykaon-cli repl                        interactive read-eval-print loop
lykaon-cli ui                          open the compiler UI (GUI build)
lykaon-cli test program.lykaon         run the Test sentences in a file
```

- `Ask` reads from the keyboard when stdin is a terminal; when stdin is not a
  terminal, `Ask` fails with *no person here* and `For each line in input.`
  streams stdin instead — this is how pipe-friendly tools are written.

## Building executables

```
lykaonc-cli build <mode> input.lykaon output
```

| Mode | Meaning |
|---|---|
| `debug` | fresh tree, no optimizer passes — closest to the interpreter |
| `fast` | optimizer passes applied, tuned for speed |
| `small` | optimizer passes applied, tuned for size |

Example:

```
lykaonc-cli build fast hello.lykaon hello.exe
```

`build` prints the optimizer report (contract prover, constant folding, inlining,
dead code, bounds-check elimination, devirtualization, whole-program passes) —
one line per pass with its change count.

The output is a standalone executable for the host platform: `.exe` on Windows,
an ELF binary on Linux. It embeds what it needs and finds the runtime library
(`lykaon_rt.lib` / `liblykaon_rt.a`) by searching its own folder, its ancestors,
`target/<profile>`, `Lykaon/target/<profile>` and `rt/target/<profile>` — so a
build run from anywhere in the workspace works. To point at a specific library,
set the environment variable:

```
set Lykaon_RT_LIB=C:\path\to\lykaon_rt.lib
```

## Command-line tools made in Lykaon

A `.lykaon` file that declares `Takes`/`Option` sentences *is* a command-line tool
once built:

```lykaon
Takes file name as text.
Option verbose is whole number.
Option log level is text defaulting to debug.

If verbose is at least 1.
    Log info starting.
Say Read file name in temporary folder.
```

```
> tool.exe --help
usage + option help, exit code 0
> tool.exe
usage text, exit code 2          (a missing Takes argument is never missing)
> tool.exe --verbose 2 --log-level info data.txt
```

- Positional arguments bind to `Takes` in order
- `--name value` (or `--name=value`) fills an `Option`; a bare `--flag` is the
  word `on` for text options
- `--help` as the first argument prints the usage text and exits 0

## Packages

A package folder holds a `Lykaon.toml`:

```lykaon
Name is myapp.
Version is 1 point 0 point 0.
Needs helpers from folder helpers.
Needs tools from git https://example.com/tools.git at version 1 point 2 point 0.
```

```
lykaon-cli add <folder-or-url>       add a dependency (folder or git URL)
lykaon-cli remove NAME               remove it
lykaon-cli update [NAME]             clone/fetch, check out the pinned tag,
                                     verify the checksum, refresh lykaon.lock
```

- Git deps are cloned into `.lykaon-cache/<name>` and pinned by tag
  (`vX.Y.Z` or `X.Y.Z`); the lock records a SHA-256 tree checksum and refuses
  a rewritten tag (`Git dependency failed (T0520)`)
- `lykaon.lock` is written and updated automatically; commit it

## Benchmarks

```
lykaon-cli bench
```

Runs the six standard benchmark programs (nbody, fannkuch, spectral_norm,
binary_trees, mandelbrot, json_parse) — compile time measured separately from
execution, median of 10 runs with a warm-up, and a checksum of the program's
output printed on every run so you can verify results yourself.

## Building from source

```
cargo build --release
```

executables land in `target/release/`. `cargo test` runs the full conformance
battery (M1a, M1b, M2, ownership, M3, M4, native differential, packages).

## Note on the two front ends

`build` belongs to `lykaonc-cli`. If you ask `lykaon-cli` to build, it reminds you:

```
the lykaon front runs the interpreter: lykaon run <file> | lykaon repl | lykaon ui
the compiler front is lykaonc-cli (build belongs there)
```
