import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set

namespace Commons.Analysis.Real

/-- The function `t ↦ log (log t) - (log t)⁻¹` has derivative
`t * ((log t + 1) / (t ^ 2 * (log t) ^ 2))` for `t > 1`. -/
lemma hasDerivAt_log_log_sub_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s => Real.log (Real.log s) - (Real.log s)⁻¹)
      (t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have h0 : HasDerivAt ((fun y => Real.log (Real.log y)) - (fun y => (Real.log y)⁻¹))
      (t⁻¹ / Real.log t - -t⁻¹ / Real.log t ^ 2) t :=
    (Real.hasDerivAt_log ht0).log hlog |>.sub ((Real.hasDerivAt_log ht0).inv hlog)
  have h : HasDerivAt (fun s => Real.log (Real.log s) - (Real.log s)⁻¹)
      (t⁻¹ / Real.log t - -t⁻¹ / Real.log t ^ 2) t :=
    h0.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => rfl))
  refine h.congr_deriv ?_
  field_simp [ht0, hlog]
  ring

/-- Continuity of the Lagarias-type integrand on intervals contained in `(1, ∞)`. -/
lemma continuousAt_mul_log_add_one_div {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun s => s * ((Real.log s + 1) / (s ^ 2 * (Real.log s) ^ 2))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  refine ContinuousAt.mul continuousAt_id ?_
  refine ContinuousAt.div ((Real.continuousAt_log ht0).add continuousAt_const) ?_ ?_
  · exact (continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2)
  · exact mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog)

theorem integral_mul_psiKfun_eq {x Y : ℝ} (hx : 1 < x) (hxY : x ≤ Y) :
    (∫ t in x..Y, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) =
      (Real.log (Real.log Y) - (Real.log Y)⁻¹) - (Real.log (Real.log x) - (Real.log x)⁻¹) := by
  have hderiv : ∀ t ∈ Set.uIcc x Y,
      HasDerivAt (fun s => Real.log (Real.log s) - (Real.log s)⁻¹)
        (t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    exact hasDerivAt_log_log_sub_inv_log (lt_of_lt_of_le hx ht.1)
  have hint : IntervalIntegrable
      (fun t => t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) volume x Y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxY]
    intro t ht
    exact (continuousAt_mul_log_add_one_div (lt_of_lt_of_le hx ht.1)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using h

end Commons.Analysis.Real