import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

namespace Commons.MeasureTheory.Function

/-- Scaling the Lebesgue measure restricted to `Ioi 0` by a positive factor.  The pushforward
measure is a scalar multiple of the original one, hence has the same null sets. -/
theorem map_mul_right_restrict_Ioi_eq_smul {c : ℝ} (hc : 0 < c) :
    Measure.map (fun t : ℝ => t * c) (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal c⁻¹ • (volume.restrict (Ioi (0 : ℝ))) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_mul_const c) hs, Measure.smul_apply,
    Measure.restrict_apply (measurable_mul_const c hs)]
  have hpre : (fun t : ℝ => t * c) ⁻¹' s ∩ Ioi 0 = (fun t : ℝ => t * c) ⁻¹' (s ∩ Ioi 0) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos h2 hc⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_left h2 hc.le⟩
  rw [hpre, Real.volume_preimage_mul_right hc.ne' (s ∩ Ioi 0),
    abs_of_pos (inv_pos.mpr hc), Measure.restrict_apply hs]
  rfl

theorem aestronglyMeasurable_comp_mul_right_Ioi {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f (t * c))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hmap := map_mul_right_restrict_Ioi_eq_smul (c := c) hc
  have hsm' : MeasureTheory.AEStronglyMeasurable f
      (Measure.map (fun t : ℝ => t * c)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [hmap]
    exact MeasureTheory.AEStronglyMeasurable.smul_measure hf (ENNReal.ofReal c⁻¹)
  have hcomp := hsm'.comp_measurable (measurable_mul_const c)
  simpa only [Function.comp_def] using hcomp

end Commons.MeasureTheory.Function