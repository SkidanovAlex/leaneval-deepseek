import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

/-- The one-dimensional Lebesgue integral of `y ↦ y⁻²` over an interval `(c, R)` with
`0 < c ≤ R`: `∫_{c<y<R} y⁻² dy = 1/c − 1/R`.  Fundamental-theorem-of-calculus
computation with antiderivative `y ↦ -y⁻¹`. -/
theorem integral_Ioo_inv_sq {c R : ℝ} (hc : 0 < c) (hcR : c ≤ R) :
    (∫ y in Set.Ioo c R, (y⁻¹ : ℝ) ^ 2) = 1 / c - 1 / R := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcR]
  have hcont : ContinuousOn (fun y : ℝ => -(y⁻¹)) (Set.Icc c R) := by
    refine ContinuousOn.neg ?_
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hc hx.1)
  have hderiv : ∀ x ∈ Set.Ioo c R, HasDerivAt (fun y : ℝ => -(y⁻¹)) ((x⁻¹)^2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hc (le_of_lt hx.1))
    have h := (hasDerivAt_inv hx0).neg
    have h2 : (-( -(x ^ 2)⁻¹) : ℝ) = (x⁻¹)^2 := by rw [neg_neg, ← inv_pow x 2]
    rw [h2] at h
    exact h
  have hint : IntervalIntegrable (fun y : ℝ => (y⁻¹)^2) MeasureTheory.volume c R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcR
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hc hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcR hcont hderiv hint]
  rw [one_div, one_div]
  ring

end Commons.Analysis.Integral