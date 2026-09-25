import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- `w ↦ ‖w‖ ^ s` is integrable on every disc in `ℂ` as soon as `s > -2`, since
`∫_{‖w‖<ρ} ‖w‖^s = 2πρ^{s+2}/(s+2)`.  The two cases needed below are the Cauchy
kernel `s = -1` and the Beurling kernel `s = α - 2` with `0 < α < 1`. -/
theorem integrableOn_norm_rpow_ball {ρ s : ℝ} (hs : -2 < s) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.ball 0 ρ) := by
  -- `ℂ` is `ℝ²`, so `finrank ℝ ℂ = 2`; the singularity `‖w‖ ^ s` is comparable to
  -- `‖w‖ ^ (-α)` with `α = -s < 2 = finrank`, hence integrable on balls.
  have hd : (1 : ℕ) ≤ Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex]; norm_num
  have hα : (-s) < (Module.finrank ℝ ℂ : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num; linarith
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := 1) (α := -s) hd hα ?_ ?_
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s), neg_neg]
    simp
  · exact (by measurability : Measurable (fun w : ℂ => ‖w‖ ^ s)).aestronglyMeasurable

end Work.CR.Flat.Cauchy
