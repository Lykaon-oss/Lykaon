//! Prove that the Cranelift Full path emits real x86-64 machine code.
//! Usage: cargo run --bin prove_native <path-to-.obj>

use object::{Object, ObjectSection, ObjectSymbol};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: prove_native <file.obj>");
    let data = std::fs::read(&path).expect("cannot read object file");
    let file = object::File::parse(&data[..]).expect("cannot parse object file");

    println!("=== Object file: {} ===", path);
    println!("Format: {:?}", file.format());
    println!("Architecture: {:?}", file.architecture());
    println!("File size: {} bytes", data.len());
    println!();

    // Sections
    println!("=== Sections ===");
    for section in file.sections() {
        let name = section.name().unwrap_or("");
        let size = section.size();
        let kind = section.kind();
        let align = section.align();
        let data = section.data().unwrap_or(&[]);
        println!(
            "  {:<16} size={:>6} align={} kind={:?} data={}",
            name,
            size,
            align,
            kind,
            if data.is_empty() {
                "<empty>"
            } else {
                "<has data>"
            }
        );
        if name == ".text" && !data.is_empty() {
            println!("    .text hex (first 96 bytes):");
            for chunk in data.chunks(16) {
                let hex: String = chunk
                    .iter()
                    .map(|b| format!("{:02x}", b))
                    .collect::<Vec<_>>()
                    .join(" ");
                let ascii: String = chunk
                    .iter()
                    .map(|b| {
                        if (*b as char).is_ascii_graphic() {
                            *b as char
                        } else {
                            '.'
                        }
                    })
                    .collect();
                println!("      {:06x}:  {:<48}  {}", 0, hex, ascii);
            }
        }
    }
    println!();

    // Symbols
    println!("=== Symbols ===");
    for symbol in file.symbols() {
        let name = symbol.name().unwrap_or("");
        if !name.is_empty() {
            println!(
                "  {} (kind={:?}, scope={:?})",
                name,
                symbol.kind(),
                symbol.scope()
            );
        }
    }
    println!();

    // Dynamic symbols / relocations
    println!("=== Relocations ===");
    for section in file.sections() {
        for (_offset, reloc) in section.relocations() {
            println!(
                "  {} +{}: {:?}",
                section.name().unwrap_or("?"),
                _offset,
                reloc.kind()
            );
        }
    }
}
