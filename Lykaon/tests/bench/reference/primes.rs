fn primes_to(n: i64) {
    let mut primes = Vec::new();
    for x in 2..=n {
        let mut is_prime = true;
        for p in &primes {
            if x % p == 0 { is_prime = false; break; }
        }
        if is_prime { primes.push(x); }
    }
    for (i, p) in primes.iter().enumerate() {
        if i > 0 { print!(", "); }
        print!("{}", p);
    }
    println!();
}

fn main() {
    primes_to(1000);
}
