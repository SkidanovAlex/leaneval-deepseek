import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Commons.Analysis.Integral

/-! Pointwise bound by a non-negative constant controls the interval integral,
without any integrability assumption on the integrand. A complete proof already
exists in `Submission/Uniformity.lean`
(`Submission.BoundedMultiplicativeFunctions.interval_le_const`). -/
lemma interval_le_const {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} {c : ℝ}
    (hfc : ∀ x, f x ≤ c) (hc : 0 ≤ c) : ∫ x in a..b, f x ≤ c * (b - a) := by
  by_cases hfi : IntervalIntegrable f volume a b
  · have hmono := intervalIntegral.integral_mono hab hfi (intervalIntegrable_const) hfc
    calc
      ∫ x in a..b, f x ≤ ∫ x in a..b, c := hmono
      _ = (b - a) • c := by rw [intervalIntegral.integral_const]
      _ = c * (b - a) := by rw [smul_eq_mul]; ring
  · have hz : ∫ x in a..b, f x = 0 := intervalIntegral.integral_undef hfi
    rw [hz]
    have hba : 0 ≤ b - a := by linarith
    exact mul_nonneg hc hba

end Commons.Analysis.Integral
