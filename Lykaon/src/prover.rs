//! The contract prover (M3b, pass 1): interval analysis over one function's
//! MIR to decide, per Ensures contract, whether its condition is PROVEN
//! always true (ch.64, M3-S35). Proven contracts are skipped at run time;
//! every unproven or disproven contract keeps its live check. Requires are
//! never skipped (they constrain the caller's inputs); the analysis only
//! reads them to narrow those inputs. Soundness rules baked in:
//!
//! * exact rational arithmetic, checked; any overflow widens to unknown,
//! * whole-number arithmetic that could leave the 64-bit domain widens to
//!   unknown — in real execution it fails T0603 instead of producing a
//!   value, and a skipped check must be unable to fail, while every whole
//!   value the runtime can hold is clamped into the domain before proofs,
//! * division, whole division and remainder by a range that may contain
//!   zero widens to unknown (the sentence could fail at run time),
//! * decimal chains get an ulp-wide relative band so run-time rounding
//!   cannot break a proven comparison; magnitudes past what rationals can
//!   track drop their wall to unknown,
//! * calls, Ask results, text-shaped values and statement-bodied MIR steps
//!   (For each / Try / Look at bodies) widen every name they write; a Give
//!   back inside such a body makes the result unknown.
//!
//! Off switch: set `Lykaon_NO_PROVER=1` to disable every skip.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use lykaon_core::mir::{self, Step};
use lykaon_core::sem::{self, E, Expr, FuncDef, Op, Program, Rel};

// ============================================================ rationals

/// An exact rational `n / d`, always reduced, `d >= 1`. Any overflow gives
/// `None`: the analysis opens up to unknown instead of guessing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Rat {
    n: i128,
    d: u128,
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, o: &Rat) -> Option<std::cmp::Ordering> {
        self.cmp(*o)
    }
}

impl Rat {
    const fn zero() -> Rat {
        Rat { n: 0, d: 1 }
    }

    fn whole(v: i64) -> Rat {
        Rat { n: v as i128, d: 1 }
    }

    fn new(n: i128, d: u128) -> Option<Rat> {
        if d == 0 {
            return None;
        }
        if n == 0 {
            return Some(Rat::zero());
        }
        let g = gcd(n.unsigned_abs(), d);
        Some(Rat {
            n: n.signum() * (n.unsigned_abs() / g) as i128,
            d: d / g,
        })
    }

    /// The exact rational value of a decimal literal. Values too big or too
    /// small for exact bookkeeping give unknown (the check stays).
    fn from_f64(x: f64) -> Option<Rat> {
        if !x.is_finite() {
            return None;
        }
        if x == 0.0 {
            return Some(Rat::zero());
        }
        let bits = x.to_bits() as u128;
        let neg = bits >> 63 == 1;
        let be = ((bits >> 52) & 0x7ff) as i32;
        let mant = bits & ((1u128 << 52) - 1);
        let (mant, exp) = if be == 0 {
            (mant, -1074i32)
        } else {
            (mant | (1u128 << 52), be - 1075)
        };
        if exp >= 0 {
            if exp > 60 {
                return None;
            }
            let n = (mant.checked_shl(exp as u32)? as i128) * if neg { -1 } else { 1 };
            Rat::new(n, 1)
        } else {
            let sh = (-exp) as u32;
            if sh > 100 {
                return None;
            }
            let d = 1u128.checked_shl(sh)?;
            Rat::new((mant as i128) * if neg { -1 } else { 1 }, d)
        }
    }

    fn neg(self) -> Rat {
        Rat {
            n: -self.n,
            d: self.d,
        }
    }

    fn add(self, o: Rat) -> Option<Rat> {
        let g = gcd(self.d, o.d);
        let l2 = o.d / g;
        let lcm = self.d.checked_mul(l2)?;
        let n = self
            .n
            .checked_mul(l2 as i128)?
            .checked_add(o.n.checked_mul((self.d / g) as i128)?)?;
        Rat::new(n, lcm)
    }

    fn sub(self, o: Rat) -> Option<Rat> {
        let g = gcd(self.d, o.d);
        let l2 = o.d / g;
        let lcm = self.d.checked_mul(l2)?;
        let n = self
            .n
            .checked_mul(l2 as i128)?
            .checked_sub(o.n.checked_mul((self.d / g) as i128)?)?;
        Rat::new(n, lcm)
    }

    fn mul(self, o: Rat) -> Option<Rat> {
        Rat::new(self.n.checked_mul(o.n)?, self.d.checked_mul(o.d)?)
    }

    fn div(self, o: Rat) -> Option<Rat> {
        if o.n == 0 {
            return None;
        }
        let n = self.n.checked_mul(o.d as i128)?;
        let d = self.d.checked_mul(o.n.unsigned_abs())?;
        Rat::new(if o.n < 0 { -n } else { n }, d)
    }

    fn cmp(self, o: Rat) -> Option<std::cmp::Ordering> {
        let a = self.n.checked_mul(o.d as i128)?;
        let b = o.n.checked_mul(self.d as i128)?;
        Some(a.cmp(&b))
    }

    fn is_int(self) -> bool {
        self.d == 1
    }

    /// Truncation toward zero (whole division and "as whole number").
    fn trunc(self) -> Rat {
        if self.d == 1 {
            self
        } else {
            Rat {
                n: self.n.signum() * (self.n.unsigned_abs() / self.d) as i128,
                d: 1,
            }
        }
    }

    /// Whether the value fits the whole-number domain (i64).
    fn in_whole_domain(self) -> bool {
        let max = i64::MAX as i128;
        let min = i64::MIN as i128;
        if self.d == 1 {
            return (min..=max).contains(&self.n);
        }
        // n / d in [min, max] runs on a positive denominator.
        match max.checked_mul(self.d as i128) {
            Some(b) => {
                if self.n > b {
                    return false;
                }
            }
            None => return false,
        }
        match min.checked_mul(self.d as i128) {
            Some(b) => self.n >= b,
            None => true, // min*d overflowed below: every n stays above it
        }
    }
}

// ============================================================ intervals

/// One wall of an interval. `exclusive` on a lower wall means values are
/// strictly greater than it; on an upper wall, strictly less. No lower
/// wall is -infinity; no upper wall is +infinity.
type Wall = Option<(Rat, bool)>;

/// A closed value interval. `dec` marks decimal-laced chains, whose walls
/// carry an ulp-wide rounding band (see `band`).
#[derive(Clone, Debug, PartialEq)]
struct Iv {
    lo: Wall,
    hi: Wall,
    dec: bool,
}

/// `None` = unknown.
type Rng = Option<Iv>;

fn singleton(v: Rat, dec: bool) -> Iv {
    Iv {
        lo: Some((v, false)),
        hi: Some((v, false)),
        dec,
    }
}

/// Union (hull). Unknown infects everything.
fn join(a: Rng, b: Rng) -> Rng {
    let (a, b) = (a?, b?);
    let lo = match (a.lo, b.lo) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => {
            if v1 == v2 {
                Some((v1, f1 && f2)) // attained if either side attains it
            } else if v1 < v2 {
                Some((v1, f1))
            } else {
                Some((v2, f2))
            }
        }
    };
    let hi = match (a.hi, b.hi) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => {
            if v1 == v2 {
                Some((v1, f1 && f2))
            } else if v1 > v2 {
                Some((v1, f1))
            } else {
                Some((v2, f2))
            }
        }
    };
    Some(Iv {
        lo,
        hi,
        dec: a.dec || b.dec,
    })
}

/// Intersection (Requires narrows one name repeatedly).
fn meet(a: Rng, b: Rng) -> Rng {
    let (a, b) = (a?, b?);
    let lo = match (a.lo, b.lo) {
        (None, w) | (w, None) => w,
        (Some((v1, f1)), Some((v2, f2))) => {
            if v1 == v2 {
                Some((v1, f1 || f2))
            } else if v1 > v2 {
                Some((v1, f1))
            } else {
                Some((v2, f2))
            }
        }
    };
    let hi = match (a.hi, b.hi) {
        (None, w) | (w, None) => w,
        (Some((v1, f1)), Some((v2, f2))) => {
            if v1 == v2 {
                Some((v1, f1 || f2))
            } else if v1 < v2 {
                Some((v1, f1))
            } else {
                Some((v2, f2))
            }
        }
    };
    Some(Iv {
        lo,
        hi,
        dec: a.dec || b.dec,
    })
}

fn incl(a: &Iv) -> (Option<Rat>, Option<Rat>) {
    (a.lo.map(|(v, _)| v), a.hi.map(|(v, _)| v))
}

/// Clamp a whole (non-decimal) interval into the 64-bit domain: every
/// whole value the runtime can hold lies in it, so this never loses a real
/// value — it only makes the model more precise where the requires were
/// one-sided.
fn clamp_domain(a: &Iv) -> Iv {
    if a.dec {
        return cut_huge(a);
    }
    let max = Rat::whole(i64::MAX);
    let min = Rat::whole(i64::MIN);
    let cl = |w: Wall, (edge, is_lo): (Rat, bool)| -> Wall {
        match w {
            None => Some((edge, false)),
            Some((v, f)) => match v.cmp(edge)? {
                // a lower wall below the domain clamps UP to the edge; an
                // upper wall above it clamps DOWN
                std::cmp::Ordering::Less if is_lo => Some((edge, false)),
                std::cmp::Ordering::Greater if !is_lo => Some((edge, false)),
                _ => Some((v, f)),
            },
        }
    };
    Iv {
        lo: cl(a.lo, (min, true)),
        hi: cl(a.hi, (max, false)),
        dec: false,
    }
}

// ---------- decimal rounding band ----------

const POW52: u128 = 1u128 << 52;

/// Relative band width: `(depth + 2) * 2` ulps around every wall.
fn band_rel(depth: usize) -> u128 {
    ((depth as u128) + 2) * 2
}

/// Widen walls away from zero by a relative band; the exclusivity flag is
/// kept (a widened wall is still never attained). A zero wall stays exactly
/// at zero — that is what keeps proofs like "the result is more than 0"
/// after "n divided by 2" alive. Values past the rational headroom drop
/// their wall to unknown right after (see `cut_huge`).
fn band(a: &Iv, depth: usize) -> Iv {
    let rel = band_rel(depth);
    let shift = |w: Wall, down: bool| -> Wall {
        let (v, excl) = w?;
        if v.n == 0 {
            return Some((v, excl)); // zero never moves; the flag carries it
        }
        // Negative walls grow in magnitude the same way: away from zero.
        let grow = down == (v.n < 0);
        let num = if grow {
            POW52.checked_add(rel)?
        } else {
            POW52.checked_sub(rel)?
        };
        let fac = Rat {
            n: num as i128,
            d: POW52,
        };
        Some((v.mul(fac)?, excl))
    };
    Iv {
        lo: shift(a.lo, true),
        hi: shift(a.hi, false),
        dec: true,
    }
}

/// Decimal magnitude guard: magnitudes past the i128 rationals' honest
/// range drop out to an unbounded (unknown) side.
const DEC_LIMIT: i128 = 1i128 << 110;

fn cut_huge(a: &Iv) -> Iv {
    let cut = |w: Wall| -> Wall {
        match w {
            Some((v, _)) if v.n.abs() >= DEC_LIMIT => None,
            w => w,
        }
    };
    Iv {
        lo: cut(a.lo),
        hi: cut(a.hi),
        dec: a.dec,
    }
}

// ---------- interval arithmetic ----------

fn add_iv(a: &Iv, b: &Iv, depth: usize) -> Option<Iv> {
    let lo = match (a.lo, b.lo) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => Some((v1.add(v2)?, f1 || f2)),
    };
    let hi = match (a.hi, b.hi) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => Some((v1.add(v2)?, f1 || f2)),
    };
    let out = Iv {
        lo,
        hi,
        dec: a.dec || b.dec,
    };
    let out = cut_huge(&out);
    Some(if out.dec { band(&out, depth) } else { out })
}

fn sub_iv(a: &Iv, b: &Iv, depth: usize) -> Option<Iv> {
    // lo = a.lo - b.hi, hi = a.hi - b.lo; a strict wall on either operand
    // makes its strict case for the combined wall.
    let lo = match (a.lo, b.hi) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => Some((v1.sub(v2)?, f1 || f2)),
    };
    let hi = match (a.hi, b.lo) {
        (None, _) | (_, None) => None,
        (Some((v1, f1)), Some((v2, f2))) => Some((v1.sub(v2)?, f1 || f2)),
    };
    let out = Iv {
        lo,
        hi,
        dec: a.dec || b.dec,
    };
    let out = cut_huge(&out);
    Some(if out.dec { band(&out, depth) } else { out })
}

fn corners4(a: &Iv, b: &Iv) -> Option<[(Rat, Rat); 4]> {
    let (alo, ahi) = incl(a);
    let (blo, bhi) = incl(b);
    match (alo, ahi, blo, bhi) {
        (Some(la), Some(ha), Some(lb), Some(hb)) => Some([(la, lb), (la, hb), (ha, lb), (ha, hb)]),
        _ => None,
    }
}

/// Min and max over folded corner results.
fn minmax4(vals: [(Rat, Rat); 4], f: impl Fn(Rat, Rat) -> Option<Rat>) -> Option<(Rat, Rat)> {
    let mut mn: Option<Rat> = None;
    let mut mx: Option<Rat> = None;
    for (x, y) in vals {
        let p = f(x, y)?;
        mn = Some(match mn {
            None => p,
            Some(m) => {
                if m.cmp(p)? == std::cmp::Ordering::Greater {
                    p
                } else {
                    m
                }
            }
        });
        mx = Some(match mx {
            None => p,
            Some(m) => {
                if m.cmp(p)? == std::cmp::Ordering::Less {
                    p
                } else {
                    m
                }
            }
        });
    }
    Some((mn?, mx?))
}

fn is_zero_singleton(a: &Iv) -> bool {
    matches!(a.lo, Some((v, _)) if v.n == 0) && matches!(a.hi, Some((v, _)) if v.n == 0)
}

/// Only fully inclusive singleton constants qualify (their strict-wall
/// variants would break the flag-carrying algebra).
fn const_of(a: &Iv) -> Option<Rat> {
    match (a.lo, a.hi) {
        (Some((v, false)), Some((w, false))) if v == w => Some(v),
        _ => None,
    }
}

/// Multiplication. With a nonzero constant other operand the wall flags
/// carry through (x > v times c keeps the strict wall — with the ends
/// swapped when c is negative); otherwise walls go inclusive and the four
/// corners decide. Unbounded sides stay unknown, except the exact-zero
/// product.
fn mul_iv(a: &Iv, b: &Iv, depth: usize) -> Option<Iv> {
    let dec = a.dec || b.dec;
    if is_zero_singleton(a) || is_zero_singleton(b) {
        return Some(Iv {
            lo: Some((Rat::zero(), false)),
            hi: Some((Rat::zero(), false)),
            dec,
        });
    }
    let by_const = |other: &Iv, c: Rat| -> Option<Iv> {
        if c.n == 0 {
            return None;
        }
        let neg = c.n < 0;
        let wall = |w: Wall| -> Option<(Rat, bool)> {
            let (v, f) = w?;
            Some((v.mul(c)?, f)) // exclusivity survives any nonzero constant
        };
        let lo = wall(if neg { other.hi } else { other.lo })?;
        let hi = wall(if neg { other.lo } else { other.hi })?;
        Some(Iv {
            lo: Some(lo),
            hi: Some(hi),
            dec,
        })
    };
    let out = if let Some(c) = const_of(b) {
        by_const(a, c)?
    } else if let Some(c) = const_of(a) {
        by_const(b, c)?
    } else {
        let cs = corners4(a, b)?;
        let (mn, mx) = minmax4(cs, |x, y| x.mul(y))?;
        Iv {
            lo: Some((mn, false)),
            hi: Some((mx, false)),
            dec,
        }
    };
    let out = cut_huge(&out);
    Some(if out.dec { band(&out, depth) } else { out })
}

/// Does the interval exclude zero (needed before any division)?
fn excludes_zero(b: &Iv) -> bool {
    match (b.lo, b.hi) {
        (Some((l, lf)), Some((h, hf))) => {
            l.n > 0 || h.n < 0 || (l.n == 0 && lf) || (h.n == 0 && hf)
        }
        (Some((l, lf)), None) => l.n > 0 || (l.n == 0 && lf),
        (None, Some((h, hf))) => h.n < 0 || (h.n == 0 && hf),
        _ => false,
    }
}

/// Real (decimal) division. Flags carry through a constant divisor;
/// otherwise walls go inclusive and the corners decide.
fn div_iv(a: &Iv, b: &Iv, depth: usize) -> Option<Iv> {
    if !excludes_zero(b) {
        return None; // division by zero can fail at run time
    }
    let by_const = |other: &Iv, c: Rat| -> Option<Iv> {
        if c.n == 0 {
            return None;
        }
        let neg = c.n < 0;
        let wall = |w: Wall| -> Option<(Rat, bool)> {
            let (v, f) = w?;
            Some((v.div(c)?, f))
        };
        let lo = wall(if neg { other.hi } else { other.lo })?;
        let hi = wall(if neg { other.lo } else { other.hi })?;
        Some(Iv {
            lo: Some(lo),
            hi: Some(hi),
            dec: true,
        })
    };
    let out = if let Some(c) = const_of(b) {
        by_const(a, c)?
    } else {
        let cs = corners4(a, b)?;
        let (mn, mx) = minmax4(cs, |x, y| if y.n == 0 { None } else { x.div(y) })?;
        Iv {
            lo: Some((mn, false)),
            hi: Some((mx, false)),
            dec: true,
        }
    };
    Some(band(&cut_huge(&out), depth))
}

/// Whole division (truncate toward zero). Divisor must exclude zero.
fn wholediv_iv(a: &Iv, b: &Iv, depth: usize) -> Option<Iv> {
    let (blo, bhi) = incl(b);
    let zero_free = matches!((blo, bhi), (Some(l), Some(h)) if l.n > 0 || h.n < 0);
    if !zero_free {
        return None;
    }
    let cs = corners4(a, b)?;
    let (mn, mx) = minmax4(cs, |x, y| {
        if y.n == 0 {
            None
        } else {
            x.div(y).map(|q| q.trunc())
        }
    })?;
    let out = Iv {
        lo: Some((mn, false)),
        hi: Some((mx, false)),
        dec: a.dec || b.dec,
    };
    if out.dec {
        // decimal ancestry: band the walls, then truncate, so values just
        // outside the walls round into the neighborhood
        let banded = band(&cut_huge(&out), depth);
        let (lo, hi) = incl(&banded);
        Some(Iv {
            lo: lo.map(|v| (v.trunc(), false)),
            hi: hi.map(|v| (v.trunc(), false)),
            dec: false,
        })
    } else {
        Some(Iv {
            lo: Some((mn, false)),
            hi: Some((mx, false)),
            dec: false,
        })
    }
}

/// Whole-domain treatment for whole chains: an arithmetic result whose
/// walls leave i64 (or run unbounded) marks a chain that can FAIL T0603 at
/// run time, so a skipped check may not rely on it — unknown instead.
/// Saturating ops clamp at the domain edges instead of failing.
fn whole_gate(out: Iv, sat: bool) -> Rng {
    if out.dec {
        return Some(cut_huge(&out));
    }
    if !sat {
        let ok = |w: &Wall| -> bool {
            match w {
                Some((v, _)) => v.in_whole_domain(),
                None => false,
            }
        };
        if !ok(&out.lo) || !ok(&out.hi) {
            return None;
        }
        return Some(out);
    }
    let max = Rat::whole(i64::MAX);
    let min = Rat::whole(i64::MIN);
    let clamp_lo = match out.lo {
        None => Some((min, false)),
        Some((v, _)) => match v.cmp(min)? {
            std::cmp::Ordering::Less | std::cmp::Ordering::Equal => Some((min, false)),
            std::cmp::Ordering::Greater => out.lo,
        },
    };
    let clamp_hi = match out.hi {
        None => Some((max, false)),
        Some((v, _)) => match v.cmp(max)? {
            std::cmp::Ordering::Greater | std::cmp::Ordering::Equal => Some((max, false)),
            std::cmp::Ordering::Less => out.hi,
        },
    };
    Some(Iv {
        lo: clamp_lo,
        hi: clamp_hi,
        dec: false,
    })
}

// ============================================================ state

/// Value sets visible at one point: names, loop counters, each counter's
/// To bound (evaluated once per invocation, ch.25), and — for per-site
/// Always analysis — the statically knowable whole-record bindings
/// (`age of value` reads inside these).
#[derive(Clone, Debug, PartialEq)]
struct State {
    names: HashMap<String, Iv>,
    counters: HashMap<usize, Iv>,
    to_ivs: HashMap<usize, Rng>,
    records: HashMap<String, Vec<(String, Rng)>>,
}

impl State {
    fn bare() -> State {
        State {
            names: HashMap::new(),
            counters: HashMap::new(),
            to_ivs: HashMap::new(),
            records: HashMap::new(),
        }
    }
}

const VISIT_CAP: u32 = 12;

// ============================================================ verdicts

#[derive(Clone, Copy, PartialEq, Debug)]
enum Verdict {
    True,
    False,
    Unknown,
}

impl Verdict {
    fn flip(self) -> Verdict {
        match self {
            Verdict::True => Verdict::False,
            Verdict::False => Verdict::True,
            Verdict::Unknown => Verdict::Unknown,
        }
    }
}

/// x > y holds for every pair?
fn gt_true(l: &Iv, r: &Iv) -> Option<bool> {
    match (l.lo, r.hi) {
        (Some((vl, fl)), Some((vr, fr))) => {
            let c = vl.cmp(vr)?;
            Some(c == std::cmp::Ordering::Greater || (c == std::cmp::Ordering::Equal && (fl || fr)))
        }
        _ => Some(false),
    }
}

/// x > y holds for no pair at all?
fn gt_false(l: &Iv, r: &Iv) -> Option<bool> {
    match (l.hi, r.lo) {
        (Some((vl, fl)), Some((vr, fr))) => {
            let c = vl.cmp(vr)?;
            Some(c == std::cmp::Ordering::Less || (c == std::cmp::Ordering::Equal && (fl || fr)))
        }
        _ => Some(false),
    }
}

fn gt_of(l: Rng, r: Rng) -> Option<Verdict> {
    let (l, r) = (l?, r?);
    if gt_true(&l, &r)? {
        return Some(Verdict::True);
    }
    if gt_false(&l, &r)? {
        return Some(Verdict::False);
    }
    Some(Verdict::Unknown)
}

/// x >= y holds for every pair: the lower wall of l sits at or above the
/// upper wall of r (walls at the same value always satisfy >=).
fn ge_of(l: Rng, r: Rng) -> Option<Verdict> {
    let (l, r) = (l?, r?);
    if let (Some((vl, _)), Some((vr, _))) = (l.lo, r.hi) {
        if vl.cmp(vr)? != std::cmp::Ordering::Less {
            return Some(Verdict::True);
        }
    }
    if gt_false(&l, &r)? {
        return Some(Verdict::False);
    }
    Some(Verdict::Unknown)
}

fn is_singleton(a: &Iv) -> Option<Rat> {
    match (a.lo, a.hi) {
        (Some((v, false)), Some((w, false))) if v == w => Some(v),
        _ => None,
    }
}

fn eq_of(l: Rng, r: Rng) -> Option<Verdict> {
    let (l, r) = (l?, r?);
    // no common value at all (disjoint, strict touching walls count):
    // Equal is false for every pair; Not is true.
    if gt_false(&l, &r)? || gt_false(&r, &l)? {
        return Some(Verdict::False);
    }
    if let (Some(a), Some(b)) = (is_singleton(&l), is_singleton(&r)) {
        if a == b {
            return Some(Verdict::True);
        }
    }
    Some(Verdict::Unknown)
}

fn cmp_verdict(c: &sem::Comp, st: &State) -> Verdict {
    let l = eval_rng(&c.l, st, 0);
    let r0 = c.r.first().and_then(|x| eval_rng(x, st, 0));
    let r1 = c.r.get(1).and_then(|x| eval_rng(x, st, 0));
    let raw = match c.rel {
        Rel::More => gt_of(l.clone(), r0),
        Rel::Less => gt_of(r0, l.clone()),
        Rel::AtLeast => ge_of(l.clone(), r0),
        Rel::AtMost => ge_of(r0, l.clone()),
        Rel::Equal => eq_of(l.clone(), r0),
        Rel::Not => eq_of(l.clone(), r0).map(|v| match v {
            Verdict::Unknown => Verdict::Unknown,
            v => v.flip(),
        }),
        Rel::Between => {
            let lo_v = ge_of(l.clone(), r0); // l >= r0
            let hi_v = ge_of(r1, l.clone()); // l <= r1  ==  r1 >= l
            match (lo_v, hi_v) {
                (Some(Verdict::False), _) | (_, Some(Verdict::False)) => Some(Verdict::False),
                (Some(Verdict::True), Some(Verdict::True)) => Some(Verdict::True),
                _ => Some(Verdict::Unknown),
            }
        }
        Rel::Close | Rel::IsEmpty | Rel::Has | Rel::Missing | Rel::There => Some(Verdict::Unknown),
    };
    match raw {
        Some(v) if c.negate => v.flip(),
        Some(v) => v,
        None => Verdict::Unknown,
    }
}

fn verdict(e: &Expr, st: &State) -> Verdict {
    match &e.e {
        E::Boolean(b) => {
            if *b {
                Verdict::True
            } else {
                Verdict::False
            }
        }
        E::AndOr(l, r, is_and) => {
            let (vl, vr) = (verdict(l, st), verdict(r, st));
            if *is_and {
                match (vl, vr) {
                    (Verdict::False, _) | (_, Verdict::False) => Verdict::False,
                    (Verdict::True, Verdict::True) => Verdict::True,
                    _ => Verdict::Unknown,
                }
            } else {
                match (vl, vr) {
                    (Verdict::True, _) | (_, Verdict::True) => Verdict::True,
                    (Verdict::False, Verdict::False) => Verdict::False,
                    _ => Verdict::Unknown,
                }
            }
        }
        E::Compare(c) => cmp_verdict(c, st),
        E::Fallback { value, default } => {
            let tv = verdict(value, st);
            if !value.can_fail {
                return tv;
            }
            // the value can fail at run time and the default answers
            if verdict(default, st) == Verdict::True {
                Verdict::True
            } else {
                Verdict::Unknown
            }
        }
        _ => Verdict::Unknown,
    }
}

// ============================================================ expression ranges

fn eval_rng(e: &Expr, st: &State, depth: usize) -> Rng {
    match &e.e {
        E::Whole(w) => Some(singleton(Rat::whole(*w), false)),
        E::Dec(x) => Rat::from_f64(*x).map(|v| singleton(v, true)),
        E::Name(n) => st.names.get(n).map(|iv| {
            if iv.dec {
                cut_huge(iv)
            } else {
                clamp_domain(iv)
            }
        }),
        E::Neg(x) => eval_rng(x, st, depth).map(|iv| Iv {
            lo: iv.hi.map(|(v, f)| (v.neg(), f)),
            hi: iv.lo.map(|(v, f)| (v.neg(), f)),
            dec: iv.dec,
        }),
        E::Binary { op, l, r } => {
            let (a, b) = match (eval_rng(l, st, depth + 1), eval_rng(r, st, depth + 1)) {
                (Some(a), Some(b)) => (a, b),
                _ => return None,
            };
            match op {
                Op::Plus | Op::CheckedPlus => add_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, false)),
                Op::Minus | Op::CheckedMinus => sub_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, false)),
                Op::Time | Op::CheckedTimes => mul_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, false)),
                Op::SaturatingPlus => add_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, true)),
                Op::SaturatingMinus => sub_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, true)),
                Op::SaturatingTimes => mul_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, true)),
                // wrapping wraps: the wrap-around values are unmodelable
                Op::WrappingPlus | Op::WrappingMinus | Op::WrappingTimes => None,
                Op::DividedBy => div_iv(&a, &b, depth + 1),
                Op::WholeDividedBy => wholediv_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, false)),
                Op::Remainder | Op::Power => None,
            }
        }
        E::DivWhole(l, r) => {
            let (a, b) = match (eval_rng(l, st, depth + 1), eval_rng(r, st, depth + 1)) {
                (Some(a), Some(b)) => (a, b),
                _ => return None,
            };
            wholediv_iv(&a, &b, depth + 1).and_then(|o| whole_gate(o, false))
        }
        E::AsWhole(x) => {
            let inner = eval_rng(x, st, depth + 1)?;
            let banded = if inner.dec { band(&cut_huge(&inner), depth + 1) } else { inner };
            let (lo, hi) = incl(&banded);
            let out = Iv {
                lo: lo.map(|v| (v.trunc(), false)),
                hi: hi.map(|v| (v.trunc(), false)),
                dec: false,
            };
            whole_gate(out, false)
        }
        E::AsDecimal(x) => {
            let inner = eval_rng(x, st, depth + 1)?;
            if inner.dec {
                return Some(cut_huge(&inner));
            }
            // whole -> decimal: exact while values fit f64's 53-bit mantissa
            let big = Rat { n: 1i128 << 53, d: 1 };
            let over = [&inner.lo, &inner.hi].iter().any(|w| {
                match w {
                    Some((v, _)) => matches!(v.cmp(big), Some(std::cmp::Ordering::Greater) | None),
                    None => true,
                }
            });
            let out = if over { band(&inner, depth + 1) } else { inner };
            Some(cut_huge(&out))
        }
        E::CopyOf(x) | E::Move(x) | E::Share(x) | E::WeakShare(x) | E::AsMaybe(x) => {
            eval_rng(x, st, deepbump(depth))
        }
        // `age of value` / `age of <kind name>`: knowable only when the
        // base binds a whole-record value this analysis knows (the per-site
        // Always analysis binds parts and the whole record; nothing else
        // is knowable, records are not a Rng)
        E::PartOf { type_name, part, base } => {
            let _ = type_name;
            match &base.e {
                E::Name(n) => match st.records.get(n) {
                    Some(parts) => parts
                        .iter()
                        .find(|(pn, _)| pn == part)
                        .and_then(|(_, pv)| pv.clone()),
                    None => None,
                },
                _ => None,
            }
        }
        E::Fallback { value, default } => {
            let xv = eval_rng(value, st, depth + 1);
            if !value.can_fail {
                return xv;
            }
            let dv = eval_rng(default, st, depth + 1);
            join(xv, dv)
        }
        E::MinMax { big, items } => {
            let mut acc: Rng = None;
            let mut all: Vec<Rng> = Vec::new();
            for it in items {
                let r = eval_rng(it, st, depth + 1);
                if r.is_none() {
                    return None;
                }
                all.push(r);
            }
            acc = all[0].clone();
            for nxt in &all[1..] {
                acc = if *big { join(acc, nxt.clone()) } else { meet(acc, nxt.clone()) };
            }
            acc
        }
        // everything text-shaped, collection-shaped, call-shaped, or
        // not-analyzed stays unknown
        E::Rem(_, _) | E::Pow(_, _) | E::Round(_, _) | E::Factorial(_) | E::AsBig(_)
        | E::AsNumber(_) | E::AsText(_) | E::Lower(_) | E::Upper(_) | E::Trimmed(_)
        | E::Normalized(_) | E::JoinedWith(_, _) | E::CountIn(_) | E::Call { .. } | E::Word(_)
        | E::It | E::Them | E::Boolean(_) | E::AndOr(_, _, _) | E::Compare(_) | E::Missing
        | E::Flat(_) | E::PatWords { .. } | E::ListOf(_) | E::PairOf(_, _) | E::FirstOf(_)
        | E::SecondOf(_) | E::LastOf(_) | E::IsEmpty(_) | E::Combine { .. }
        | E::ApplyEach { .. }
        | E::Sorted(_, _) | E::Reverse(_) | E::Unique(_) | E::CollEmpty { .. }
        | E::ItemN { .. } | E::SafeItemN { .. } | E::ItemsRange { .. } | E::FirstN { .. }
        | E::Where { .. } | E::FirstFib(_) | E::PrimesTo(_) | E::AsDyn { .. } | E::FnRef(_)
        | E::PositionOf { .. } | E::ValueOf { .. } | E::Has { .. } | E::Union { .. }
        | E::Overlap { .. } | E::Difference { .. } | E::Split { .. } | E::Replace { .. }
        | E::RecordOf { .. } | E::EnumOf { .. }
        // M4 (Appendix K): copies/guarded cells and channel/atomic
        // constructions are outside the interval model; a file question
        // (M4-5) reads the disk, far outside it too
        | E::ChannelOf { .. } | E::GuardedOf(_) | E::AtomicNum | E::CounterZero
        | E::FileExists(_)
        // M4-6 (7.6): json of x turns a value into text - nothing the
        // interval model holds
        | E::JsonOf(_)
        // M4-10 (7.8): a request read is outside the interval model too
        | E::RequestRead { .. }
        // M4-7 (7.7): the time, random and secret reads hold nothing
        // the interval model tracks either
        | E::DateCtor { .. } | E::Today | E::Now | E::MomentAt { .. }
        | E::InZone { .. } | E::TimeShift { .. } | E::DurationOf { .. }
        | E::DaysBetween { .. } | E::SecondsBetween { .. } | E::RandomRange { .. }
        | E::RandomDec | E::RandomItem { .. } | E::Shuffled { .. }
        | E::HashOf(_) | E::SecretOf(_) | E::Reveal(_)
        // M4-8: the environment and input reads are outside the interval
        // model
        | E::Environment { .. } | E::ReadInput => None,
    }
}

// Copy-of-family reads the same value; a small depth bump keeps bands honest.
fn deepbump(depth: usize) -> usize {
    depth + 1
}

// ============================================================ the skip gate

pub fn children(e: &Expr) -> Vec<&Expr> {
    match &e.e {
        E::Neg(x) | E::Round(x, _) | E::Factorial(x) | E::CountIn(x) | E::Lower(x) | E::Upper(x)
        | E::Trimmed(x) | E::Normalized(x) | E::AsWhole(x) | E::AsDecimal(x) | E::AsBig(x)
        | E::AsText(x) | E::AsNumber(x) | E::AsMaybe(x) | E::CopyOf(x) | E::Move(x) | E::Share(x)
        | E::WeakShare(x) | E::FirstOf(x) | E::SecondOf(x) | E::LastOf(x) | E::IsEmpty(x)
        | E::Sorted(x, _) | E::Reverse(x) | E::Unique(x) | E::FirstFib(x) | E::PrimesTo(x) => {
            vec![x]
        }
        E::JoinedWith(x, _) => vec![x],
        E::Binary { l, r, .. } | E::DivWhole(l, r) | E::Rem(l, r) | E::Pow(l, r) => vec![l, r],
        E::Union { a, b } | E::Overlap { a, b } | E::Difference { a, b } => vec![a, b],
        E::AndOr(l, r, _) => vec![l, r],
        E::PairOf(l, r) | E::Split { text: l, sep: r } => vec![l, r],
        E::ListOf(v) | E::Flat(v) => v.iter().collect(),
        E::MinMax { items, .. } => items.iter().collect(),
        E::Combine { list, .. } | E::ApplyEach { list, .. } => vec![list],
        E::Fallback { value, default } => vec![value, default],
        E::RecordOf { parts, .. } | E::EnumOf { parts, .. } => parts.iter().map(|(_, e)| e).collect(),
        E::PartOf { base, .. } => vec![base],
        E::ItemN { list, n } | E::SafeItemN { list, n } => vec![list, n],
        E::ItemsRange { list, from, to } => vec![list, from, to],
        E::FirstN { list, n } => vec![list, n],
        E::Where { list, cond } => vec![list, cond],
        E::AsDyn { value, .. } => vec![value],
        E::PositionOf { haystack, needle } | E::ValueOf { map: haystack, key: needle }
        | E::Has { coll: haystack, item: needle } => vec![haystack, needle],
        E::Replace { pat, repl, text } => vec![pat, repl, text],
        E::Call { args, .. } => args.iter().collect(),
        E::Compare(c) => {
            let mut v = vec![&*c.l];
            for x in &c.r {
                v.push(x);
            }
            v
        }
        E::Boolean(_)
        | E::Missing
        | E::Word(_)
        | E::It
        | E::Them
        | E::FnRef(_)
        | E::PatWords { .. }
        | E::CollEmpty { .. }
        | E::Whole(_)
        | E::Dec(_)
        | E::Name(_) => Vec::new(),
        // M4 (Appendix K): guarded V holds V; a channel/atomic/counter
        // construction holds nothing the skip gate needs; a file
        // question (M4-5) holds no sub expression (and never proves
        // always-true, so its check stays live)
        E::GuardedOf(x) => vec![x],
        E::ChannelOf { .. } | E::AtomicNum | E::CounterZero | E::FileExists(_)
        // M4-6: json of x keeps its own can-fail flag (the inner's) so
        // the skip gate holds without walking inside
        | E::JsonOf(_)
        // M4-10 (7.8): a request read holds no sub expression
        | E::RequestRead { .. }
        // M4-7 (7.7): the time, random and secret reads keep their own
        // can-fail flags the same way
        | E::DateCtor { .. } | E::Today | E::Now | E::MomentAt { .. }
        | E::InZone { .. } | E::TimeShift { .. } | E::DurationOf { .. }
        | E::DaysBetween { .. } | E::SecondsBetween { .. } | E::RandomRange { .. }
        | E::RandomDec | E::RandomItem { .. } | E::Shuffled { .. }
        | E::HashOf(_) | E::SecretOf(_) | E::Reveal(_) => Vec::new(),
        // M4-8 (7.10/7.11): the environment and input reads hold no
        // sub expression
        E::Environment { .. } | E::ReadInput => Vec::new(),
    }
}

/// A skipped condition must be unable to fail at run time: no calls (they
/// can fail, say, or have other effects) and no failing conversion.
fn skippable(e: &Expr) -> bool {
    if e.can_fail {
        return false;
    }
    if matches!(e.e, E::Call { .. }) {
        return false;
    }
    let mut stack = children(e);
    while let Some(x) = stack.pop() {
        if x.can_fail || matches!(x.e, E::Call { .. }) {
            return false;
        }
        stack.extend(children(x));
    }
    true
}

// ============================================================ requires -> input ranges

/// Narrow `name`'s lower wall inside `env`.
fn bound_lo(env: &mut HashMap<String, Iv>, name: &str, v: Rat, excl: bool) {
    let e = env.entry(name.to_string()).or_insert(Iv {
        lo: None,
        hi: None,
        dec: false,
    });
    e.lo = match e.lo {
        None => Some((v, excl)),
        Some((old, oldf)) => {
            if old == v {
                Some((old, oldf || excl))
            } else if old < v {
                Some((old, oldf))
            } else {
                Some((v, excl))
            }
        }
    };
}

fn bound_hi(env: &mut HashMap<String, Iv>, name: &str, v: Rat, excl: bool) {
    let e = env.entry(name.to_string()).or_insert(Iv {
        lo: None,
        hi: None,
        dec: false,
    });
    e.hi = match e.hi {
        None => Some((v, excl)),
        Some((old, oldf)) => {
            if old == v {
                Some((old, oldf || excl))
            } else if old > v {
                Some((old, oldf))
            } else {
                Some((v, excl))
            }
        }
    };
}

/// The exact rational of a literal-shaped expression (whole, decimal, or
/// their negation); `None` for anything else.
fn literal_rat(e: &Expr) -> Option<Rat> {
    match &e.e {
        E::Whole(w) => Some(Rat::whole(*w)),
        E::Dec(x) => Rat::from_f64(*x),
        E::Neg(inner) => literal_rat(inner).map(|v| v.neg()),
        _ => None,
    }
}

fn extract_requires(cond: &Expr, env: &mut HashMap<String, Iv>) {
    if let E::AndOr(l, r, true) = &cond.e {
        extract_requires(l, env);
        extract_requires(r, env);
        return;
    }
    let E::Compare(c) = &cond.e else { return };
    if c.negate {
        return; // negated shapes: the pass-1 analysis leaves them alone
    }
    fn name_side(e: &Expr) -> Option<&String> {
        match &e.e {
            E::Name(n) => Some(n),
            _ => None,
        }
    }
    match c.rel {
        Rel::More | Rel::Less | Rel::AtLeast | Rel::AtMost | Rel::Equal => {
            let Some(v0s) = c.r.first() else { return };
            let (nl, nr) = (name_side(&c.l), name_side(v0s));
            if let (Some(n), None) = (nl, nr) {
                let Some(v) = literal_rat(v0s) else { return };
                match c.rel {
                    Rel::More => bound_lo(env, n, v, true),
                    Rel::AtLeast => bound_lo(env, n, v, false),
                    Rel::Less => bound_hi(env, n, v, true),
                    Rel::AtMost => bound_hi(env, n, v, false),
                    Rel::Equal => {
                        bound_lo(env, n, v, false);
                        bound_hi(env, n, v, false);
                    }
                    _ => unreachable!(),
                }
            } else if let (None, Some(n)) = (nl, nr) {
                let Some(v) = literal_rat(&c.l) else { return };
                match c.rel {
                    Rel::More => bound_hi(env, n, v, true),     // v > n
                    Rel::Less => bound_lo(env, n, v, true),     // v < n
                    Rel::AtLeast => bound_hi(env, n, v, false), // v <= n
                    Rel::AtMost => bound_lo(env, n, v, false),  // v >= n
                    Rel::Equal => {
                        bound_lo(env, n, v, false);
                        bound_hi(env, n, v, false);
                    }
                    _ => unreachable!(),
                }
            }
        }
        Rel::Between => {
            if let Some(n) = name_side(&c.l) {
                if c.r.len() == 2 {
                    if let (Some(v0), Some(v1)) = (literal_rat(&c.r[0]), literal_rat(&c.r[1])) {
                        bound_lo(env, n, v0, false);
                        bound_hi(env, n, v1, false);
                    }
                }
            }
        }
        Rel::Close | Rel::Not | Rel::IsEmpty | Rel::Has | Rel::Missing | Rel::There => {}
    }
}

// ============================================================ the body scanner

/// Statement-bodied MIR steps hide their writes from the block graph, so
/// every name such a body may write is widened here; a Give back inside
/// makes the function's result unknown.
fn scan_stmts(stmts: &[sem::Stmt], st: &mut State, gave: &mut bool) {
    for s in stmts {
        match s {
            sem::Stmt::Note => {}
            sem::Stmt::Define(d) => {
                st.names.remove(&d.name);
                // its value expression is evaluated through the normal
                // eval path; unknown shapes already widen the bound name
            }
            sem::Stmt::Set { name, .. } => {
                st.names.remove(name);
            }
            sem::Stmt::Ask { name, .. } => {
                st.names.remove(name);
            }
            sem::Stmt::Say { .. } => {}
            // M4-9 (7.12): Log writes to the error stream and Use log
            // level only changes it; neither touches a name.
            sem::Stmt::Log { .. } | sem::Stmt::LogLevel { .. } => {}
            // M4-10 (7.8): Fetch/Post/WsRecv leave a fresh result in it;
            // the server bodies run inline and walk.
            sem::Stmt::Fetch { .. } | sem::Stmt::PostTo { .. } | sem::Stmt::WsRecv { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::Serve { body, .. } | sem::Stmt::WhenSomeone { body, .. }
            | sem::Stmt::WhenLive { body, .. } => scan_stmts(body, st, gave),
            sem::Stmt::Respond { .. } | sem::Stmt::PageDecl { .. } | sem::Stmt::WsSend { .. } => {}
            sem::Stmt::Careful { body } => scan_stmts(body, st, gave),
            sem::Stmt::If { branches, other } => {
                for (_, b) in branches {
                    scan_stmts(b, st, gave);
                }
                if let Some(o) = other {
                    scan_stmts(o, st, gave);
                }
            }
            sem::Stmt::RepeatTimes { body, .. }
            | sem::Stmt::RepeatForever { body }
            | sem::Stmt::RepeatWhile { body, .. }
            | sem::Stmt::ForRange { body, .. } => scan_stmts(body, st, gave),
            sem::Stmt::ForIn { vars, body, .. } => {
                for v in vars {
                    st.names.remove(v);
                }
                scan_stmts(body, st, gave);
            }
            sem::Stmt::Evaluate { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::Append { list, .. }
            | sem::Stmt::Put { map: list, .. }
            | sem::Stmt::Remove { coll: list, .. }
            | sem::Stmt::RemoveFirst { coll: list } => {
                st.names.remove(list);
            }
            sem::Stmt::SetPart { path, .. } => {
                if let Some(holder) = path.first() {
                    st.names.remove(holder);
                }
            }
            sem::Stmt::LookAt { whens, .. } => {
                for w in whens {
                    for n in &w.names {
                        st.names.remove(n);
                    }
                    scan_stmts(&w.body, st, gave);
                }
            }
            sem::Stmt::DefineEnum { .. } => {}
            sem::Stmt::Try { sentence, success, failure } => {
                scan_stmts(std::slice::from_ref(sentence), st, gave);
                scan_stmts(success, st, gave);
                for (bind, arm) in failure {
                    if let Some(n) = bind {
                        st.names.remove(n);
                    }
                    scan_stmts(arm, st, gave);
                }
            }
            sem::Stmt::Fail { .. } | sem::Stmt::PassFailureUp => {}
            sem::Stmt::Close { .. } | sem::Stmt::Share { .. } | sem::Stmt::Use { .. } => {}
            sem::Stmt::Test { body, .. } | sem::Stmt::Check { body, .. } => {
                scan_stmts(body, st, gave)
            }
            sem::Stmt::Pretend { name, .. } => {
                st.names.remove(name);
            }
            sem::Stmt::Stop | sem::Stmt::Skip => {}
            sem::Stmt::GiveBack(_) | sem::Stmt::HandBack(_) => {
                *gave = true;
            }
            sem::Stmt::DefineLocalFn(_) => {}
            // M4 (Appendix K): the eager first cut runs task/together bodies
            // inline, so their writes are walked like any other body; a Give
            // back inside a task makes the encloser's result unknown too.
            // Wait for produces it/them.
            sem::Stmt::StartTask { body, .. } | sem::Stmt::DoTogether { body } => {
                scan_stmts(body, st, gave)
            }
            sem::Stmt::WaitFor { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::StopTask { .. } | sem::Stmt::SleepFor { .. } => {}
            // M4 (Appendix K): AtomicAdd writes its target in one step the
            // prover does not value - widen that name. Send writes only
            // channel state the prover never reads. Receive produces it/them.
            sem::Stmt::AtomicAdd { name, .. } => {
                st.names.remove(name);
            }
            sem::Stmt::Send { .. } => {}
            sem::Stmt::Receive { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            // M4-4 (Appendix K 7.3/7.4): a spread round and a stream round
            // run inline in this cut (it/them produced; the stream loop
            // defines its variable); timer rounds run on the sleep calendar
            // or at main end, but a due round CAN fire mid-flow during a
            // Sleep, so their bodies are walked too (conservative).
            sem::Stmt::Spread { body, .. } => {
                st.names.remove("it");
                st.names.remove("them");
                scan_stmts(body, st, gave);
            }
            sem::Stmt::StreamLoop { var, body, .. } => {
                st.names.remove(var);
                st.names.remove("it");
                st.names.remove("them");
                scan_stmts(body, st, gave);
            }
            sem::Stmt::AfterTimer { body, .. } | sem::Stmt::EveryTimer { body, .. } => {
                scan_stmts(body, st, gave)
            }
            sem::Stmt::UseWorkers { .. } => {}
            // M4-7 (7.7): Use seed touches nothing.
            sem::Stmt::UseSeed { .. } => {}
            // M4-8 (7.10/7.11): Run produces it (the child's standard
            // output); the signal and input loop bodies run inline (a Give
            // back inside widens the result); Exit writes nothing.
            sem::Stmt::RunProc { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::Exit { .. } => {}
            // M4-10 (7.8): Fetch/Post/WsRecv leave a fresh result in it;
            // the server bodies run inline and walk.
            sem::Stmt::Fetch { .. } | sem::Stmt::PostTo { .. } | sem::Stmt::WsRecv { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::Serve { body, .. } | sem::Stmt::WhenSomeone { body, .. }
            | sem::Stmt::WhenLive { body, .. } => scan_stmts(body, st, gave),
            sem::Stmt::Respond { .. } | sem::Stmt::PageDecl { .. } | sem::Stmt::WsSend { .. } => {}
            sem::Stmt::Careful { body } => scan_stmts(body, st, gave),
            sem::Stmt::WhenSignal { body, .. } => scan_stmts(body, st, gave),
            sem::Stmt::ForEachInput { var, body, .. } => {
                st.names.remove(var);
                st.names.remove("it");
                st.names.remove("them");
                scan_stmts(body, st, gave);
            }
            // M4-5 (Appendix K 7.5): the file sentences. A read/list
            // lands its result in it; the for-each-line var and a
            // temporary file name are written here; the loop/watch
            // bodies can write anything (walked).
            sem::Stmt::ReadFile { .. } | sem::Stmt::ReadBytes { .. }
            | sem::Stmt::ListFolder { .. } => {
                st.names.remove("it");
                st.names.remove("them");
            }
            sem::Stmt::WriteFile { .. } | sem::Stmt::AppendFile { .. }
            | sem::Stmt::ReplaceFile { .. } | sem::Stmt::MakeFolder { .. }
            | sem::Stmt::RemovePath { .. } | sem::Stmt::MovePath { .. }
            | sem::Stmt::DuplicatePath { .. } | sem::Stmt::ZipOp { .. }
            // M4-6 (7.6): the save (a write shape) and the format reads
            | sem::Stmt::SaveFormat { .. } | sem::Stmt::ReadFormat { .. }
            | sem::Stmt::ReadFormatText { .. } => {}
            sem::Stmt::MakeTempFile { name } => {
                st.names.remove(name);
            }
            sem::Stmt::ForEachLine { var, body, .. } => {
                st.names.remove(var);
                st.names.remove("it");
                st.names.remove("them");
                scan_stmts(body, st, gave)
            }
            sem::Stmt::WhenFileChanges { body, .. } => scan_stmts(body, st, gave),
        }
    }
}

// ============================================================ the MIR walker

struct Walker {
    blocks: Vec<mir::Block>,
    states: HashMap<usize, State>,
    visits: HashMap<usize, u32>,
    queue: Vec<usize>,
    /// Give back value ranges joined over all reachable give-backs; `None`
    /// streaming in from unknown or body-hidden ones poisons the whole.
    /// `got` separates "no give-back seen yet" from "first one was unknown".
    result: Option<Iv>,
    got: bool,
    poisoned: bool,
}

impl Walker {
    fn enqueue(&mut self, id: usize, st: State) {
        match self.states.get_mut(&id) {
            None => {
                self.states.insert(id, st);
                self.queue.push(id);
            }
            Some(old) => {
                if *old == st {
                    return; // fixpoint on this edge
                }
                let cap_hit = self.visits.get(&id).copied().unwrap_or(0) > VISIT_CAP;
                if cap_hit {
                    // widen: any name still moving becomes unknown
                    old.names.clear();
                    old.counters.clear();
                    old.to_ivs.clear();
                } else {
                    for (k, iv) in old.names.clone() {
                        match join(Some(iv), st.names.get(&k).cloned()) {
                            Some(nv) => {
                                old.names.insert(k, nv);
                            }
                            None => {
                                old.names.remove(&k);
                            }
                        }
                    }
                    for (k, iv) in old.counters.clone() {
                        match join(Some(iv), st.counters.get(&k).cloned()) {
                            Some(nv) => {
                                old.counters.insert(k, nv);
                            }
                            None => {
                                old.counters.remove(&k);
                            }
                        }
                    }
                    for (k, iv) in old.to_ivs.clone() {
                        match join(iv, st.to_ivs.get(&k).cloned().flatten()) {
                            Some(nv) => {
                                old.to_ivs.insert(k, Some(nv));
                            }
                            None => {
                                old.to_ivs.remove(&k);
                            }
                        }
                    }
                    // bindings this path introduces that the merged state
                    // does not know yet join in as-is
                    for (k, iv) in st.names.clone() {
                        if !old.names.contains_key(&k) {
                            old.names.insert(k, iv);
                        }
                    }
                    for (k, iv) in st.counters.clone() {
                        if !old.counters.contains_key(&k) {
                            old.counters.insert(k, iv);
                        }
                    }
                    for (k, iv) in st.to_ivs.clone() {
                        if !old.to_ivs.contains_key(&k) {
                            old.to_ivs.insert(k, iv);
                        }
                    }
                }
                if !self.queue.contains(&id) {
                    self.queue.push(id);
                }
            }
        }
    }

    fn run(mut self, entry: usize, seed: State) -> Option<Iv> {
        self.states.insert(entry, seed);
        self.queue.push(entry);
        while let Some(b) = self.queue.pop() {
            let mut st = self
                .states
                .get(&b)
                .cloned()
                .expect("queued blocks always have state");
            *self.visits.entry(b).or_default() += 1;
            let mut flowed = false; // control left mid-block
            let steps = self.blocks[b].steps.clone();
            for step in &steps {
                match step {
                    Step::Define { name, eval, .. } | Step::Set { name, eval, .. } => {
                        match eval_rng(eval, &st, 0) {
                            Some(iv) => {
                                let iv = if iv.dec {
                                    cut_huge(&iv)
                                } else {
                                    clamp_domain(&iv)
                                };
                                st.names.insert(name.clone(), iv);
                            }
                            None => {
                                st.names.remove(name);
                            }
                        }
                    }
                    Step::Ask { name, .. } => {
                        st.names.remove(name);
                    }
                    Step::DefineCounter { name, counter } => match st.counters.get(counter) {
                        Some(iv) => {
                            let iv = if iv.dec {
                                cut_huge(iv)
                            } else {
                                clamp_domain(iv)
                            };
                            st.names.insert(name.clone(), iv);
                        }
                        None => {
                            st.names.remove(name);
                        }
                    },
                    Step::ForInit { counter, from, to } => {
                        match eval_rng(from, &st, 0) {
                            Some(iv) => {
                                let iv = if iv.dec {
                                    cut_huge(&iv)
                                } else {
                                    clamp_domain(&iv)
                                };
                                st.counters.insert(*counter, iv);
                            }
                            None => {
                                st.counters.remove(counter);
                            }
                        }
                        st.to_ivs.insert(*counter, eval_rng_opt(to.as_ref(), &st));
                    }
                    Step::ForCheck { counter, yes, no } => {
                        // yes side: the counter has not passed its To bound
                        // (the To value is fixed per invocation, ch.25)
                        let mut sy = st.clone();
                        if let Some(civ) = sy.counters.get(counter).cloned() {
                            let cap = sy.to_ivs.get(counter).cloned().flatten();
                            if let Some(t) = cap {
                                let capped = meet(
                                    Some(civ),
                                    Some(Iv {
                                        lo: None,
                                        hi: t.hi,
                                        dec: false,
                                    }),
                                );
                                match capped {
                                    Some(c) => {
                                        sy.counters.insert(*counter, c);
                                    }
                                    None => {
                                        sy.counters.remove(counter);
                                    }
                                }
                            }
                        }
                        self.enqueue(yes.block, sy);
                        self.enqueue(no.block, st.clone());
                        flowed = true;
                        break;
                    }
                    Step::Advance {
                        counter,
                        step,
                        target,
                    } => {
                        if let Some(civ) = st.counters.get(counter).cloned() {
                            let ste = singleton(Rat::whole(*step), false);
                            match add_iv(&civ, &ste, 0) {
                                Some(n) => {
                                    let lim = if n.dec {
                                        cut_huge(&n)
                                    } else {
                                        clamp_domain(&n)
                                    };
                                    st.counters.insert(*counter, lim);
                                }
                                None => {
                                    st.counters.remove(counter);
                                }
                            }
                        }
                        self.enqueue(target.block, st.clone());
                        flowed = true;
                        break;
                    }
                    Step::GiveBack { value } => {
                        let r = value.as_ref().and_then(|e| eval_rng(e, &st, 0));
                        match r {
                            Some(iv) => {
                                if self.got {
                                    if let Some(old) = self.result.take() {
                                        self.result = join(Some(old), Some(iv));
                                    } else {
                                        self.poisoned = true;
                                    }
                                } else {
                                    self.result = Some(iv);
                                    self.got = true;
                                }
                            }
                            // an unknown give-back value, or a bare Give
                            // back, hides the function's result
                            None => {
                                self.poisoned = true;
                                self.result = None;
                            }
                        }
                        flowed = true;
                        break;
                    }
                    Step::HandBack { .. } => {
                        // generator items: pass 1 leaves generators alone
                        self.poisoned = true;
                        flowed = true;
                        break;
                    }
                    Step::Stop { target, .. } | Step::Skip { target, .. } => {
                        self.enqueue(*target, st.clone());
                        flowed = true;
                        break;
                    }
                    Step::Fail | Step::FailStmt { .. } | Step::PassFailureUp => {
                        // the run aborts here; no result value flows out
                        flowed = true;
                        break;
                    }
                    Step::Branch { cond, yes, no } => {
                        let mut jumped = false;
                        if let Some(t) = yes {
                            self.enqueue(t.block, st.clone());
                            jumped = true;
                        }
                        if cond.is_some() {
                            if let Some(t) = no {
                                self.enqueue(t.block, st.clone());
                                jumped = true;
                            }
                        }
                        if jumped {
                            flowed = true;
                            break;
                        }
                    }
                    // statement-bodied steps and the opaque rest
                    Step::ForEach { var, body, .. } => {
                        st.names.remove(var);
                        let mut gave = false;
                        scan_stmts(body, &mut st, &mut gave);
                        if gave {
                            self.poisoned = true;
                        }
                    }
                    Step::Try {
                        sentence,
                        success,
                        failure,
                    } => {
                        let mut gave = false;
                        scan_stmts(std::slice::from_ref(sentence), &mut st, &mut gave);
                        scan_stmts(success, &mut st, &mut gave);
                        for (bind, arm) in failure {
                            if let Some(n) = bind {
                                st.names.remove(n);
                            }
                            scan_stmts(arm, &mut st, &mut gave);
                        }
                        if gave {
                            self.poisoned = true;
                        }
                    }
                    Step::LookAt { whens, .. } => {
                        let mut gave = false;
                        for w in whens {
                            for n in &w.names {
                                st.names.remove(n);
                            }
                            scan_stmts(&w.body, &mut st, &mut gave);
                        }
                        if gave {
                            self.poisoned = true;
                        }
                    }
                    Step::Test { body, .. } | Step::Check { body, .. } => {
                        let mut gave = false;
                        scan_stmts(body, &mut st, &mut gave);
                        if gave {
                            self.poisoned = true;
                        }
                    }
                    Step::Evaluate { result_var, .. } => {
                        st.names.remove(result_var);
                    }
                    Step::Say { .. }
                    | Step::SayLines { .. }
                    | Step::DefineLocalFn { .. }
                    | Step::Append { .. }
                    | Step::Put { .. }
                    | Step::Remove { .. }
                    | Step::RemoveFirst { .. }
                    | Step::SetPart { .. }
                    | Step::DefineEnum { .. }
                    | Step::Close { .. }
                    | Step::Share { .. }
                    | Step::Use { .. }
                    | Step::Pretend { .. } => {}
                    // M4: the evaluator sentences (channels, tasks, timers,
                    // files, formats, system, log, network) run through
                    // the original statement code; the prover sees nothing
                    // through them (conservative, as before)
                    Step::Other => {}
                }
            }
            if !flowed {
                if let Some(t) = &self.blocks[b].exit {
                    self.enqueue(t.block, st);
                }
            }
        }
        if self.poisoned { None } else { self.result }
    }
}

fn eval_rng_opt(e: Option<&Expr>, st: &State) -> Rng {
    match e {
        Some(x) => eval_rng(x, st, 0),
        None => None,
    }
}

// ============================================================ public analysis

/// For one function: per Ensures contract, whether the condition is proven
/// always true under the Requires-narrowed input ranges and the analyzed
/// give-back values.
pub fn analyze_ensures(f: &sem::FuncDef) -> Vec<bool> {
    if f.ensures.is_empty() {
        return Vec::new();
    }
    let mut env: HashMap<String, Iv> = HashMap::new();
    for rc in &f.requires {
        extract_requires(&rc.cond, &mut env);
    }
    let (pmir, entry) = mir::build_fn_body(f);
    let seed = State {
        names: env.clone(),
        counters: HashMap::new(),
        to_ivs: HashMap::new(),
        records: HashMap::new(),
    };
    let walker = Walker {
        blocks: pmir.blocks,
        states: HashMap::new(),
        visits: HashMap::new(),
        queue: Vec::new(),
        result: None,
        got: false,
        poisoned: false,
    };
    let Some(result) = walker.run(entry, seed) else {
        return vec![false; f.ensures.len()];
    };
    let mut names = env;
    names.insert("result".to_string(), result);
    let venv = State {
        names,
        counters: HashMap::new(),
        to_ivs: HashMap::new(),
        records: HashMap::new(),
    };
    f.ensures
        .iter()
        .map(|c| {
            let v = verdict(&c.cond, &venv);
            // proven if the interval pass decides it, and (pass 2, M3b-5)
            // only behind the "smt" feature, whether Z3 proves NOT cond
            // unsatisfiable under the same required bounds. Anything else
            // keeps the run-time check.
            let proven = match v {
                Verdict::True => true,
                #[cfg(feature = "smt")]
                Verdict::Unknown => smt_pass::cond_is_tautology(&c.cond, &venv),
                #[cfg(not(feature = "smt"))]
                Verdict::Unknown => false,
                _ => false,
            };
            proven && skippable(&c.cond)
        })
        .collect()
}

/// ============================================================
/// Pass 2: Z3 re-check for conditions the interval pass cannot decide
/// (M3b-5, behind the "smt" feature — the plain build never links Z3 and
/// behaves exactly as before). Thecondition is encoded over integer
/// variables bounded by the Requires-narrowed ranges; `NOT cond` SAT means
/// a counterexample exists, so the check stays. Unsat = proven true.
#[cfg(feature = "smt")]
mod smt_pass {
    use super::{E, Expr, Op, Rat, State, sem};
    use std::collections::HashMap;
    use z3::ast::{Ast, Bool, Int};
    use z3::{Config, Context, SatResult, Solver};

    /// Is `cond` provably true for every value the state's bounds allow?
    /// Anything that is not whole-number arithmetic bails out and stays
    /// checked (sound: skipping is only ever an answer of "no").
    pub fn cond_is_tautology(cond: &Expr, state: &State) -> bool {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut enc = Enc {
            ctx: &ctx,
            vars: HashMap::new(),
            bailed: false,
        };
        let Some(f) = enc.bool_of(cond) else {
            return false;
        };
        if enc.bailed {
            return false;
        }
        let solver = Solver::new(&ctx);
        // Required ranges from the interval pass become bounds. Only exact
        // whole walls in-range for i64 become assumptions; anything looser
        // is simply left out (fewer assumptions can only leave a check in).
        for (name, iv) in &state.names {
            if iv.dec {
                continue;
            }
            if let Some((v, open)) = &iv.lo {
                if let Some(w) = wall_i64(v) {
                    let x = enc.var(name);
                    let b = if *open {
                        x.gt(&Int::from_i64(&ctx, w))
                    } else {
                        x.ge(&Int::from_i64(&ctx, w))
                    };
                    solver.assert(&b);
                }
            }
            if let Some((v, open)) = &iv.hi {
                if let Some(w) = wall_i64(v) {
                    let x = enc.var(name);
                    let b = if *open {
                        x.lt(&Int::from_i64(&ctx, w))
                    } else {
                        x.le(&Int::from_i64(&ctx, w))
                    };
                    solver.assert(&b);
                }
            }
        }
        let notf = !f;
        solver.assert(&notf);
        solver.check() == SatResult::Unsat
    }

    /// One integer wall value; anything else keeps the run-time check
    fn wall_i64(v: &Rat) -> Option<i64> {
        if v.d == 1 {
            i64::try_from(v.n).ok()
        } else {
            None
        }
    }

    struct Enc<'ctx> {
        ctx: &'ctx Context,
        vars: HashMap<String, Int<'ctx>>,
        bailed: bool,
    }

    impl<'ctx> Enc<'ctx> {
        fn var(&mut self, name: &str) -> Int<'ctx> {
            let key = name.to_ascii_lowercase();
            if let Some(v) = self.vars.get(&key) {
                return v.clone();
            }
            let v = Int::new_const(self.ctx, key.clone());
            self.vars.insert(key, v.clone());
            v
        }

        fn bool_of(&mut self, e: &Expr) -> Option<Bool<'ctx>> {
            if self.bailed {
                return None;
            }
            if e.kind != sem::Kind::Boolean {
                self.bailed = true;
                return None;
            }
            match &e.e {
                E::Boolean(b) => Some(if *b {
                    // TRUE := 0 == 0; FALSE := 0 > 0
                    Int::from_i64(self.ctx, 0)._eq(&Int::from_i64(self.ctx, 0))
                } else {
                    Int::from_i64(self.ctx, 0).gt(&Int::from_i64(self.ctx, 0))
                }),
                E::AndOr(l, r, is_and) => {
                    let bl = self.bool_of(l)?;
                    let br = self.bool_of(r)?;
                    Some(if *is_and {
                        Bool::and(self.ctx, &[&bl, &br])
                    } else {
                        Bool::or(self.ctx, &[&bl, &br])
                    })
                }
                E::Compare(c) => self.compare(c),
                // `X as text fallback Y` in a condition: if X cannot fail at
                // run time the default is unreachable, so encode X alone.
                // If X can fail (a text-to-number conversion) there is no
                // honest encoding - the check stays.
                E::Fallback { value, .. } if !value.can_fail => self.bool_of(value),
                _ => {
                    self.bailed = true;
                    None
                }
            }
        }

        fn int_of(&mut self, e: &Expr) -> Option<Int<'ctx>> {
            if self.bailed {
                return None;
            }
            if e.kind != sem::Kind::Whole {
                self.bailed = true;
                return None;
            }
            match &e.e {
                E::Whole(v) => Some(Int::from_i64(self.ctx, *v)),
                E::Name(n) => Some(self.var(n)),
                E::Neg(a) => Some(self.int_of(a)?.unary_minus()),
                E::Binary { op, l, r } => self.binary(*op, l, r),
                // `A whole divided by B` and remainder: Z3's integer div and
                // rem round toward negative infinity while the language
                // truncates toward zero, so a proof over one would not say
                // the truth about the other (e.g. (0-7) whole divided
                // by 2 is -3 at run time, -4 in SMT-LIB div). The condition
                // keeps its run-time check instead of being proven by a
                // slightly different arithmetic.
                E::DivWhole(..) | E::Rem(..) => {
                    self.bailed = true;
                    None
                }
                E::Pow(b, k) if matches!(&k.e, E::Whole(n) if *n >= 0 && *n <= 8) => {
                    let (E::Whole(n), x) = (&k.e, self.int_of(b)?) else {
                        unreachable!()
                    };
                    // x^0 = 1; otherwise n straight multiplications
                    if *n == 0 {
                        Some(Int::from_i64(self.ctx, 1))
                    } else {
                        let refs: Vec<Int<'ctx>> = (0..*n).map(|_| x.clone()).collect();
                        let borrows: Vec<&Int<'ctx>> = refs.iter().collect();
                        Some(Int::mul(self.ctx, &borrows))
                    }
                }
                _ => {
                    // text/collection/record/decimal/checked-math nodes:
                    // the run-time check stays
                    self.bailed = true;
                    None
                }
            }
        }

        fn binary(&mut self, op: Op, l: &Expr, r: &Expr) -> Option<Int<'ctx>> {
            let li = self.int_of(l)?;
            let ri = self.int_of(r)?;
            match op {
                Op::Plus => Some(Int::add(self.ctx, &[&li, &ri])),
                Op::Minus => Some(Int::sub(self.ctx, &[&li, &ri])),
                Op::Time => Some(Int::mul(self.ctx, &[&li, &ri])),
                // unchecked raw math equals the language here? The language
                // gives decimals for DividedBy and distinct behavior for
                // checked/wrapping/saturating variants, so leave those to
                // pass 1 rather than guess.
                _ => {
                    self.bailed = true;
                    None
                }
            }
        }

        fn compare(&mut self, c: &sem::Comp) -> Option<Bool<'ctx>> {
            let l = self.int_of(&c.l)?;
            let r0 = self.int_of(c.r.first()?)?;
            let base = match c.rel {
                sem::Rel::Equal => l._eq(&r0),
                // `x is not y` is the same predicate negated
                sem::Rel::Not => (!r0._eq(&l)),
                sem::Rel::More => l.gt(&r0),
                sem::Rel::Less => l.lt(&r0),
                sem::Rel::AtLeast => l.ge(&r0),
                sem::Rel::AtMost => r0.ge(&l),
                sem::Rel::Between => {
                    let r1 = self.int_of(c.r.get(1)?)?;
                    Bool::and(self.ctx, &[&l.ge(&r0), &l.le(&r1)])
                }
                sem::Rel::Close
                | sem::Rel::IsEmpty
                | sem::Rel::Has
                | sem::Rel::Missing
                | sem::Rel::There => {
                    self.bailed = true;
                    return None;
                }
            };
            if c.negate { Some(!base) } else { Some(base) }
        }
    }
}

// ============================================================ per-site Always analysis (M3b-3)

/// For one SITE (a record construction or a Set part write), per Always
/// condition of the kind: whether the condition is proven always true for
/// every value the site can build. `parts` carries ONLY the statically
/// knowable part values (at a construction site every part's expression;
/// at a Set-part site the written part alone). A part whose value is not
/// knowable here is simply left unbound — every condition that reads it
/// stays unknown and keeps its run-time check.
pub fn analyze_site_always(conds: &[Expr], type_name: &str, parts: &[(String, Expr)]) -> Vec<bool> {
    if conds.is_empty() {
        return Vec::new();
    }
    let mut st = State::bare();
    let mut rec: Vec<(String, Rng)> = Vec::new();
    for (n, e) in parts {
        let iv = eval_rng(e, &st, 0);
        if let Some(v) = &iv {
            let v = if v.dec { cut_huge(v) } else { clamp_domain(v) };
            st.names.insert(n.clone(), v);
        }
        rec.push((n.clone(), iv));
    }
    // the whole-record bindings mirror run_always: the kind name, `value`
    // and `original`, skipped when a part itself has that name
    for name in [type_name, "value", "original"] {
        if !parts.iter().any(|(n, _)| n == name) {
            st.records.insert(name.to_string(), rec.clone());
        }
    }
    conds
        .iter()
        .map(|c| verdict(c, &st) == Verdict::True && skippable(c))
        .collect()
}

// ============================================================ install + report

static OFF: OnceLock<bool> = OnceLock::new();

fn off() -> bool {
    *OFF.get_or_init(|| {
        std::env::var("Lykaon_NO_PROVER")
            .map(|v| !v.is_empty() && v != "0")
            .unwrap_or(false)
    })
}

static INSTALLED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Wire the analysis into the interpreter: the Ensures skip hook and the
/// per-site Always hook; idempotent, called from the single compile
/// funnel. `Lykaon_NO_PROVER` disables both.
pub fn install() {
    if !INSTALLED.swap(true, std::sync::atomic::Ordering::SeqCst) {
        lykaon_core::interp::install_prover_hook(hook);
        lykaon_core::interp::install_always_hook(always_hook);
    }
}

fn hook(f: &FuncDef) -> Arc<Vec<bool>> {
    if off() {
        Arc::new(vec![false; f.ensures.len()])
    } else {
        Arc::new(analyze_ensures(f))
    }
}

fn always_hook(type_name: &str, parts: &[(String, Expr)], conds: &[Expr]) -> Arc<Vec<bool>> {
    if off() {
        Arc::new(vec![false; conds.len()])
    } else {
        Arc::new(analyze_site_always(conds, type_name, parts))
    }
}

/// How many Ensures contracts the prover removes in this program (used by
/// `lykaon build --report`; M3b-6 wires it into benchmarks).
pub fn proof_counts(prog: &Program) -> usize {
    let mut n = 0;
    for f in &prog.funcs {
        n += analyze_ensures(f).iter().filter(|v| **v).count();
    }
    for imp in &prog.impls {
        for f in &imp.funcs {
            n += analyze_ensures(f).iter().filter(|v| **v).count();
        }
    }
    n
}

/// How many per-site Always checks (record constructions and one-level Set
/// part writes) the prover proves skippable in this program. Counts, like
/// the interpreter, come from the same site facts the skip consumes.
pub fn site_counts(prog: &mut Program) -> usize {
    let conds_by_kind: HashMap<String, Vec<Expr>> =
        prog.always.iter().fold(HashMap::new(), |mut m, (tn, c)| {
            m.entry(tn.clone()).or_default().push(c.cond.clone());
            m
        });
    let mut n = 0usize;
    crate::optimizer::every_list(prog, &mut |list: &mut Vec<sem::Stmt>| {
        // names that hold a statically typed record in this list: a
        // one-level Set part write reads the kind from where the record
        // was built (the interpreter reads it from the run-time value)
        let mut name_kinds: HashMap<String, String> = HashMap::new();
        for st in list.iter() {
            if let sem::Stmt::Define(d) = st {
                if let E::RecordOf { type_name, .. } = &d.expr.e {
                    name_kinds.insert(d.name.to_ascii_lowercase(), type_name.clone());
                }
            }
        }
        for st in list.iter_mut() {
            // one-level Set part writes: Set <part> of <name>, where the
            // written value's expression is statically knowable
            if let sem::Stmt::SetPart { path, expr } = st {
                if path.len() == 2 {
                    // path runs [<part name>, <record name>]: the written
                    // part is first, the record's name last (the
                    // interpreter takes the name off the end)
                    let rec_name = &path[path.len() - 1];
                    let kind = name_kinds.get(&rec_name.to_ascii_lowercase()).cloned();
                    if let Some(tn) = kind {
                        if let Some(cs) = conds_by_kind.get(&tn) {
                            let known = vec![(path[0].clone(), expr.clone())];
                            n += analyze_site_always(cs, &tn, &known)
                                .into_iter()
                                .filter(|b| *b)
                                .count();
                        }
                    }
                }
            }
            // record construction sites anywhere inside the statement's
            // expressions
            crate::optimizer::map_stmt_exprs(st, &mut |ex: &mut Expr| {
                walk_expr_sites(ex, &conds_by_kind, &mut n);
            });
        }
    });
    n
}

/// Count provable RecordOf sites in one expression subtree.
fn walk_expr_sites(e: &Expr, conds_by_kind: &HashMap<String, Vec<Expr>>, n: &mut usize) {
    if let E::RecordOf { type_name, parts } = &e.e {
        if let Some(cs) = conds_by_kind.get(type_name) {
            *n += analyze_site_always(cs, type_name, parts.as_slice())
                .into_iter()
                .filter(|b| *b)
                .count();
        }
    }
    for c in children(e) {
        walk_expr_sites(c, conds_by_kind, n);
    }
}

/// Total contract checks this prover removes for one program: proven
/// Ensures contracts (per function) plus proven always sites. This is the
/// number `lykaon build --report` and `lykaon bench` surface (M3b-6).
pub fn checks_removed(prog: &mut Program) -> usize {
    proof_counts(prog) + site_counts(prog)
}
