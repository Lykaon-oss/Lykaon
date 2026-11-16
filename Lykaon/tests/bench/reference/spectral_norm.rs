fn spectral(n: i64) -> i64 {
    if n <= 0 { return 1; }
    if n == 1 { return 2; }
    let a = std::hint::black_box(spectral(n - 1));
    let b = std::hint::black_box(spectral(n - 2));
    let c = std::hint::black_box(spectral(n - 3));
    a + b + c + n
}

fn main() {
    println!("{}", std::hint::black_box(spectral(32)));
}
