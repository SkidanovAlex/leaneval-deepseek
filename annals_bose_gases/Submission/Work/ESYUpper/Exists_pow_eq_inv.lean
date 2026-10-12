import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYUpper

/-- For every positive real `x` and every `N ≥ 1`, the positive real `x⁻¹` has a
`(2 * N)`-th root, namely `exp (-(log x) / (2 * N))`. -/
theorem Exists_pow_eq_inv {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    ∃ s : ℝ, s ^ (2 * N) = x⁻¹ := by
  refine ⟨Real.exp (-(Real.log x) / (2 * N)), ?_⟩
  rw [← Real.exp_nat_mul]
  have h2N : ((2 * N : ℕ) : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]
    omega
  have hmul : ((2 * N : ℕ) : ℝ) * (-(Real.log x) / (2 * N)) = -(Real.log x) := by
    field_simp
    push_cast
    ring
  rw [hmul, Real.exp_neg, Real.exp_log hx]

end Work.ESYUpper
