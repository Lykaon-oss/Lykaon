fn mandel(n: i64) -> i64 {
    if n <= 0 { return 1; }
    if n == 1 { return 2; }
    let a = std::hint::black_box(mandel(n - 1));
    let b = std::hint::black_box(mandel(n - 2));
    a + 2 * b + n
}

fn main() {
    println!("{}", std::hint::black_box(mandel(40)));
}
