import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

/-!
# The finite certificate for `Margin.caC1` in region II (part B, `10^5 ≤ ξ < 10^8`)

`Margin.caC1 ε = ∑_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³))`, and in region II we may take the sum
over the primes in `(n, 10^5]`, where `n = ⌊√(2.5ξ)⌋₊ + 1`:

`caC1 ε ≥ ∑_{n < q ≤ 10^5, q prime} (1/(2q²) − 1/(3q³)) =: Tail (n-1)`,

because `ξ₂ ≤ n` and `10^5 ≤ ξ`.  The right hand side is a *decreasing* step function of the
integer cutoff `j = n - 1 ∈ [500, 15811]`, and the requirement

`(43/100)·u(ξ) ≤ Tail j`,   `u(ξ) = 1/(√ξ log ξ)`,

becomes weakest on each run of constancy at the *smallest* `j` of the run, i.e. at the cutoffs
`501, 503, 509, … , 15809` (a cutoff `501` is added artificially, since for `n ∈ {501,502}` the
sum starts at the prime `503`).  At a cutoff `j` the requirement is bounded by

`(43/100)·u(ξ) ≤ (43/100)·√2.5 / (j·(2 log j − log 2.5)) ≤ 688·10^9/(j·(2⌊10^9 log j⌋ − A))`,

with `A = utOf 5 − ltOf 2 ≥ 10^9 log 2.5` and `688 ≥ (43/100)·1.6 ≥ (43/100)√2.5`.

This file sets up the integer certificate: `c1num q = ⌊10^40 (1/(2q²) − 1/(3q³))⌋`, the
descending list of cutoffs, the accumulator recursion `tailsFrom` producing the pairs
`(cutoff, tail sum)`, and the single `decide` check `cert_check` over all `1750` cutoffs
`≤ 15812`.  The mathematical extraction lives in the sibling files.
-/

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket

/-- Scale of the integer certificate: `10^40`. -/
def certScale : ℕ := 10 ^ 40

/-- `⌊10^40 · c1 q⌋`, where `c1 q = 1/(2q²) − 1/(3q³) = (3q − 2)/(6q³)`. -/
def c1num (q : ℕ) : ℕ := (3 * q - 2) * certScale / (6 * q ^ 3)

/-- The ascending list of cutoffs: the integer `501` together with every prime in
`(501, 10^5]`.  (`CU` is the certified table of all primes `≤ 100003`.) -/
def certAsc : List ℕ := 501 :: ((CU.map Prod.fst).filter (fun q => 501 < q && q ≤ 100000))

/-- The same cutoffs in descending order. -/
def certDesc : List ℕ := certAsc.reverse

/-- The `(cutoff, tail sum)` pairs.  The accumulator recursion runs over the descending list,
so the value paired with `p` is the sum of the `c1num` over the cutoffs *greater* than `p`. -/
def tailsFrom : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | p :: ps, acc => (p, acc) :: tailsFrom ps (acc + c1num p)

/-- `10^9 log 2.5` bounded above by the certified brackets of `log 5` and `log 2`. -/
def certA : ℕ := utOf 5 - ltOf 2

/-- The single integer check: for every cutoff `p ≤ 15812`, the tail sum `t` satisfies
`688·10^46 ≤ t·(p−1)·(2⌊10^9 log(p−1)⌋ − 10^9 log 2.5)`. -/
def certOk (pr : ℕ × ℕ) : Bool :=
  decide (15812 < pr.1) ||
    decide (688 * 10 ^ 46 ≤ pr.2 * (pr.1 - 1) * (2 * ltOf (pr.1 - 1) - certA))

set_option maxRecDepth 1000000 in
/-- **The certificate**: all `1750` cutoffs `p ≤ 15812` pass the check. -/
theorem cert_check : (tailsFrom certDesc 0).all certOk = true := by decide

/-- The value of the constant `A`. -/
theorem certA_eq : certA = 918173000 := rfl

end Work.RHContract.A.regionII
