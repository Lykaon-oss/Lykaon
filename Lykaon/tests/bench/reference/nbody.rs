fn nbody(n: i64) -> i64 {
    if n <= 0 { return 1; }
    let a = std::hint::black_box(nbody(n - 1));
    let b = std::hint::black_box(nbody(n - 2));
    a + b + n
}

fn main() {
    println!("{}", std::hint::black_box(nbody(40)));
}
