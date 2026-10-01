import Mathlib

open MeasureTheory

namespace Work.ZeroFreeTables.P9F

/-- For `z ≠ 0`, the integral of `t ↦ exp (-(z * t))` over `[0, X]` equals
`(1 - exp (-(z * X))) / z`. -/
theorem integral_exp_neg_mul (z X : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..X, Real.exp (-(z * t)) = (1 - Real.exp (-(z * X))) / z := by
  -- Fundamental theorem of calculus with primitive `t ↦ -(exp (-(z * t)) / z)`,
  -- whose derivative is `t ↦ exp (-(z * t))`.
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun y : ℝ => -(Real.exp (-(z*y))/z)) (Real.exp (-(z*x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -(z * y)) (-z) x := by
      have h : HasDerivAt (fun y : ℝ => z * y) z x := by
        simpa using (hasDerivAt_id x).const_mul z
      exact h.neg
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(z*y))) (Real.exp (-(z*x)) * (-z)) x := h1.exp
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(z*y))/z) (Real.exp (-(z*x)) * (-z) / z) x :=
      h2.div_const z
    exact (h3.neg).congr_deriv (by rw [mul_neg, neg_div, neg_neg, mul_div_cancel_right₀ _ hz])
  have hint : IntervalIntegrable (fun y : ℝ => Real.exp (-(z*y))) volume (0:ℝ) X :=
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-(z*y))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

end Work.ZeroFreeTables.P9F
