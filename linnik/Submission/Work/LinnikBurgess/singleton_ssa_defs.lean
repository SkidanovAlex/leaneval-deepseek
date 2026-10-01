import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.DdBits

/-!
# Auxiliary definitions for the U13 assembly `Work.LinnikBurgess.singleton_sum_all`

`q` is a positive modulus.  Writing `e_p = q.factorization p`, the primes of `q` split into

* `lowPrimeSet q`  : those with `e_p = 1` (the squarefree part of `q`),
* `highPrimeSet q` : those with `2 ≤ e_p`.

At a prime of the second kind the local bound `localFactor_bound_ge5` / `localFactor_bound_small`
applies; at a prime of the first kind the Weil-type bound `local_prime_sqrtWeight` applies.  The
product of the latter carries the weight `∏_p sqrtGcdW p i v`, which is compared with
`sqrtGcdW (sqfreePart q) i v` so that `frame_count` can be applied with `m = sqfreePart q`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-- The *squarefree part* of `q`: the product of the primes whose exponent in `q` is exactly `1`.
For `q = 0` (not used) `primeFactors 0 = ∅`, so `sqfreePart 0 = 1`. -/
noncomputable def sqfreePart (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => q.factorization p = 1), p

/-- The primes of `q` whose exponent in `q` is `1`. -/
def lowPrimeSet (q : ℕ) : Finset ℕ := q.primeFactors.filter (fun p => q.factorization p = 1)

/-- The primes of `q` whose exponent in `q` is at least `2`. -/
def highPrimeSet (q : ℕ) : Finset ℕ := q.primeFactors.filter (fun p => 2 ≤ q.factorization p)

/-- The local bound attached to a prime `p` of `q` with exponent `e`:
`6 √p · W_p(v)` when `e = 1` and `p^{e/2} · localFactor p e a b` when `e ≥ 2`. -/
noncomputable def localB (i : Fin 6) (a b : Fin 3 → ℕ) (p e : ℕ) : ℝ :=
  if e = 1 then 6 * Real.sqrt (p : ℝ) * sqrtGcdW p i (shift a b)
  else (p : ℝ) ^ ((e : ℝ) / 2) * localFactor p e a b

end Work.LinnikBurgess
