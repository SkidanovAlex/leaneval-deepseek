import Mathlib
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz

namespace Commons.Analysis.Integral

open MeasureTheory Set

/-- The function `t ↦ (log(|t|+2)+1)/(1+t²)` is integrable on `ℝ`: the logarithmic growth is
beaten by the quadratic decay, and it is dominated by a constant multiple of
`(1+t²)^{-3/4}`, which is integrable. -/
theorem integrable_log_add_div_one_add_sq :
    MeasureTheory.Integrable (fun t : ℝ => (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) MeasureTheory.volume := by
  set M : ℝ := Real.log 3 + 3 with hM
  have hlog_cont : Continuous (fun t : ℝ => Real.log (|t| + 2)) :=
    (continuous_id.abs.add continuous_const).log (fun t => ne_of_gt (by positivity : (0:ℝ) < |t| + 2))
  have hcont : Continuous (fun t : ℝ => (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) := by
    apply Continuous.div
    · exact (hlog_cont.add continuous_const)
    · fun_prop
    · intro t; positivity
  have hdom : Integrable (fun t : ℝ => M * (1 + t ^ 2) ^ (-((3:ℝ)/4))) volume :=
    (integrable_one_add_sq_rpow_neg ((3:ℝ)/4) (by norm_num)).const_mul M
  refine Integrable.mono' hdom hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
  have hden : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hnum_nonneg : 0 ≤ Real.log (|t| + 2) + 1 := by
    have : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hf_nonneg : 0 ≤ (Real.log (|t| + 2) + 1) / (1 + t ^ 2) := div_nonneg hnum_nonneg hden.le
  rw [Real.norm_of_nonneg hf_nonneg]
  have hlogt : Real.log (|t| + 2) + 1 ≤ M * (1 + t ^ 2) ^ ((1:ℝ)/4) := by
    have h := log_two_add_abs_le 0 t
    simp only [abs_zero, add_zero, sub_zero] at h
    rw [hM, add_comm (|t|) 2]
    exact h
  calc (Real.log (|t| + 2) + 1) / (1 + t ^ 2)
      = (Real.log (|t| + 2) + 1) * (1 + t ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (M * (1 + t ^ 2) ^ ((1:ℝ)/4)) * (1 + t ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hlogt (by positivity)
    _ = M * ((1 + t ^ 2) ^ ((1:ℝ)/4) * (1 + t ^ 2)⁻¹) := by ring
    _ = M * (1 + t ^ 2) ^ (-((3:ℝ)/4)) := by
        rw [← Real.rpow_neg_one (1 + t^2),
            ← Real.rpow_add (by positivity : (0:ℝ) < 1 + t^2)]
        congr 1; norm_num

end Commons.Analysis.Integral
