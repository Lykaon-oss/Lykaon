fn json_parse(n: i64) -> i64 {
    if n <= 0 { return 1; }
    if n == 1 { return 3; }
    let a = std::hint::black_box(json_parse(n - 1));
    let b = std::hint::black_box(json_parse(n - 2));
    let c = std::hint::black_box(json_parse(n - 3));
    a + b + c + n * 2
}

fn main() {
    println!("{}", std::hint::black_box(json_parse(32)));
}
