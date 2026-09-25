import Mathlib
import Submission.Work.Beltrami.dbarW_cauchyT_defs
import Submission.Work.Beltrami.tendsto_cutK_mul

namespace Work.Beltrami

open MeasureTheory

/-- The cutoff kernel `cutK ε` is the Cauchy kernel `u ↦ u⁻¹` multiplied by the
bounded radial cutoff `u ↦ ψ(‖u‖²/ε² - 1)`.  Hence `g * cutK ε` is dominated
pointwise (indeed everywhere) by `‖g u * u⁻¹‖`, and the latter is integrable for
continuous compactly supported `g`. -/
theorem integrable_mul_cutK {g : ℂ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (ε : ℝ) :
    MeasureTheory.Integrable (fun u => g u * cutK ε u) MeasureTheory.volume := by
  have hbase : MeasureTheory.Integrable (fun u : ℂ => g u * u⁻¹) MeasureTheory.volume :=
    integrable_mul_inv g hg hgc
  refine hbase.norm.mono' ?_ ?_
  · exact (hg.measurable.mul (measurable_cutK ε)).aestronglyMeasurable
  · filter_upwards with u
    calc ‖g u * cutK ε u‖ = ‖g u‖ * ‖cutK ε u‖ := norm_mul _ _
      _ ≤ ‖g u‖ * ‖u⁻¹‖ := mul_le_mul_of_nonneg_left (norm_cutK_le ε u) (norm_nonneg _)
      _ = ‖g u * u⁻¹‖ := (norm_mul _ _).symm

end Work.Beltrami
