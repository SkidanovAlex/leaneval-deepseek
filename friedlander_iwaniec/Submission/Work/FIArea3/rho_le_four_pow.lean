import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea1.Nsol_le_tau_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea3

/-- **The number of solutions of `a² + b² ≡ 0 (mod d)` is at most `d·τ(d)`.**

  `ρ(d) := #{(a,b) ∈ (ℤ/d)² : a² + b² ≡ 0} ≤ d·τ(d)`  for `d ≥ 1`.

(An earlier draft claimed `ρ(d) ≤ 4^{ω(d)}·d`; a reviewer refuted it at `d = 625 = 5⁴`, where
`ρ = 2625 > 2500 = 4·625`, because `ρ(p^k)/p^k = 1 + k(1 - 1/p)` grows *linearly* in `k`.  The
correct bound carries the exponent `k_p = v_p(d)` through the divisor function.)

This is the local-density bound that makes the count `card_gBox_filter_dvd_gnorm` summable:
together with `Σ_{d ≤ X} τ(d)/d ≪ (log X)²` and `Σ_{d ≤ X} d·τ(d) ≪ X²log X` (partial summation
from `Σ_{d≤X}τ(d) ≪ X log X`, `Commons.NumberTheory.DivisorSum.sum_tau_mul_log_le`) it gives
`Σ_{z ∈ gBox R} τ(|z|²) = Σ_d #{z : d ∣ |z|²} ≪ (2R+1)²(log R)^{O(1)}` — the *average* of `τ(|z|²)`
over a box, replacing the pointwise maximum `2^{(log N)/(log log x)²}`.  It is also the exact
constant coined in `Commons.NumberTheory.Diophantine.disk_congruence_count`.

**Proof sketch.**  `ρ` is multiplicative (CRT, `a² + b² ≡ 0` splits over the prime powers), and for
`p^k` the solutions are described by Hensel: for `p ≡ 1 (mod 4)` one gets the exact
`ρ(p^k) = p^k + k·p^{k-1}(p-1) = p^k(1 + k(1-1/p)) ≤ p^k(k+1)` (the `a ≡ ±i b` branches plus the
`p`-adic approximations of `b = 0`, `a = 0`); for `p ≡ 3 (mod 4)` and odd `k` there are none beyond
`a ≡ b ≡ 0`, and for `p ≡ 2` a similar count; in every case `ρ(p^k) ≤ p^k(k+1)`.  Therefore
`ρ(d) = ∏_{p | d} ρ(p^{v_p(d)}) ≤ ∏_p p^{k_p}(k_p+1) = d·τ(d)`.

(A cheaper route to the same statement: `ρ(d) = Σ_{b mod d} #{a : a² ≡ -b²}`; for each `b` the
solutions form at most `2·gcd(b, R)·`(square-root-of-`-1` count) classes with `R` the square part,
and a careful Hensel count of the `p`-adic branches gives `ρ(p^k) ≤ p^k(k+1)` directly.  The naive
`Σ_b gcd(b,R) ≤ d·2^{ω(R)}` is **false** for non-squarefree `R` — a reviewer flagged this — so the
`p`-adic computation must be done per prime power.) -/
theorem rho_le_four_pow (d : ℕ) (hd : 1 ≤ d) :
    ({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard ≤ d * d.divisors.card :=
  Work.FIArea1.Nsol_le_tau_mul d hd

end Work.FIArea3
