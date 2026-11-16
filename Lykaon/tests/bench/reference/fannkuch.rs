fn fib(n: i64) -> i64 {
    if n <= 1 { return n; }
    let a = std::hint::black_box(fib(n - 1));
    let b = std::hint::black_box(fib(n - 2));
    a + b
}

fn main() {
    println!("{}", std::hint::black_box(fib(42)));
}
