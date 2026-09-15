import Mathlib
import Submission.Commons.Measure.EuclideanSpace.integrableOn_abs_log_sum_sq
import Submission.Commons.Measure.EuclideanSpace.integrable_log_sum_sq_mul

open MeasureTheory

namespace Commons.Measure.EuclideanSpace

/-- Pointwise identity: `|t| * c = t * c + 2 * (max 0 (-t) * c)`. -/
private lemma abs_mul_eq_add_max_mul (t c : ℝ) :
    |t| * c = t * c + 2 * (max 0 (-t) * c) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [abs_of_neg ht, max_eq_right (neg_nonneg.mpr ht.le)]; ring
  · rw [abs_of_nonneg ht, max_eq_left (neg_nonpos.mpr ht)]; ring

theorem integrable_abs_log_sum_sq_mul {d : ℕ} (hd : 1 ≤ d) (ψ : (Fin d → ℂ) → ℝ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun z : Fin d → ℂ => |Real.log (∑ j, ‖z j‖ ^ 2)| * ψ z)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  obtain ⟨M, hM⟩ := hψs.exists_bound_of_continuous hψc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  -- the (nonnegative part of the) negative logarithm, weighted by `ψ`
  have hg : Integrable (fun z : Fin d → ℂ => max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)))
      (volume : Measure (Fin d → ℂ)) := integrable_max_zero_neg_log_sum_sq hd
  have hgψ : Integrable
      (fun z : Fin d → ℂ => max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) * ψ z)
      (volume : Measure (Fin d → ℂ)) := by
    have hmeas : AEStronglyMeasurable
        (fun z : Fin d → ℂ => max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) * ψ z)
        (volume : Measure (Fin d → ℂ)) := by
      apply Measurable.aestronglyMeasurable
      measurability
    refine Integrable.mono' (hg.const_mul M) hmeas ?_
    filter_upwards with z
    have hgz : 0 ≤ max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) := le_max_left _ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgz]
    calc max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) * |ψ z|
        ≤ max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) * M :=
          mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hM z) hgz
      _ = M * max 0 (-Real.log (∑ j, ‖z j‖ ^ 2)) := by ring
  -- decomposition of the absolute value
  refine (Integrable.add (integrable_log_sum_sq_mul hd ψ hψc hψs) (hgψ.mul_const 2)).congr ?_
  filter_upwards with z
  simp only [Pi.add_apply]
  rw [abs_mul_eq_add_max_mul]
  ring

end Commons.Measure.EuclideanSpace
