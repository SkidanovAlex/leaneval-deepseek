import Mathlib
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.B.lcm_transfer_defs`

The vocabulary of ROUTE_LEAD §3.1 (Lemma T, the elementary transfer at `n = lcm(1..⌊x⌋)`):

* `lcmExp x p = ⌊log ⌊x⌋ / log p⌋` is the exponent of the prime `p` in `lcm(1..⌊x⌋₊)`
  (Mathlib: `(Nat.lcmUpto ⌊x⌋₊).factorization p = Nat.log p ⌊x⌋₊`).

* `lcmCorr x` is the correction term `B_L` of the proof: writing
  `σ(N)/N = ∏_{p ≤ ⌊x⌋₊} (1 + 1/p + … + 1/p^{e_p})` with `N = lcm(1..⌊x⌋₊)` and
  `e_p = lcmExp x p`, one has `1 + 1/p + … + 1/p^{e_p} = (1 - p^{-(e_p+1)})/(1 - 1/p)`, so

      log (σ(N)/N) = logRatioSum x − lcmCorr x ,
      lcmCorr x = Σ_{p ≤ ⌊x⌋₊} −log (1 − p^{-(e_p+1)}) ≥ 0 .

  The elementary bound `lcmCorr x ≤ 5/√x` (for `x ≥ 100`) is the "step 5" of the route.
-/

namespace Work.RHContract.B

open scoped ArithmeticFunction.sigma
open Finset

/-- The exponent of the prime `p` in `lcm(1..⌊x⌋₊)`. -/
noncomputable def lcmExp (x : ℝ) (p : ℕ) : ℕ := Nat.log p ⌊x⌋₊

/-- The correction term `B_L(x) = Σ_{p ≤ ⌊x⌋₊} -log(1 - p^{-(e_p+1)})`,
`e_p = lcmExp x p` being the exponent of `p` in `lcm(1..⌊x⌋₊)`. -/
noncomputable def lcmCorr (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - 1 / (p : ℝ) ^ (Nat.log p ⌊x⌋₊ + 1))

lemma lcmExp_eq (x : ℝ) (p : ℕ) : lcmExp x p = Nat.log p ⌊x⌋₊ := rfl

end Work.RHContract.B
