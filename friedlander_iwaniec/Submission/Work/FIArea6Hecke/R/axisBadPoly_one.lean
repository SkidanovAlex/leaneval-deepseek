import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

/-! ## The correction at `d = 1`

`G_d(s) = ∏_{p | 4d} (1 - p^{-s})(1 - χ₄(p) p^{-s})` (see `AxisLogDefs`).  For `d = 1` the only
bad prime is `2`, and `χ₄(2) = 0`; hence `G_1(s) = 1 - 2^{-s}`, the Euler factor at `2` of the
Dedekind zeta function of `ℚ(i)` (which is exactly the factor removed by passing from `ζ·L(χ₄)`
to the principal Hecke `L`-function, all primary elements being odd). -/

/-- `2` is the only prime factor of `2`. -/
lemma primeFactors_two : Nat.primeFactors 2 = {2} := by
  rw [Nat.primeFactors, Nat.primeFactorsList_prime Nat.prime_two]
  simp

/-- `2` is the only prime factor of `4`. -/
lemma primeFactors_four : (4 * 1).primeFactors = {2} := by
  rw [show (4 * 1 : ℕ) = 2 ^ 2 by norm_num,
    Nat.primeFactors_pow _ (by norm_num), primeFactors_two]

theorem axisBadPoly_one (s : ℂ) :
    Work.FIArea6Hecke.R.axisBadPoly 1 s = 1 - (2 : ℂ) ^ (-s) := by
  rw [axisBadPoly, primeFactors_four, Finset.prod_singleton]
  simp [axisChi4]

end Work.FIArea6Hecke.R
