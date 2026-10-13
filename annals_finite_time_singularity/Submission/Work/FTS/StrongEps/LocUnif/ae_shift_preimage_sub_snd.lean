import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- **Almost-everywhere statements transfer under a vertical translation.**  The
second-coordinate analogue of `ae_shift_preimage_sub`: if `Q` holds almost everywhere on `A`,
and the shift `q ↦ (q.1, q.2 - h)` maps `B` into `A`, then `Q` holds almost everywhere on `B`
after the shift.  Only the translation invariance of Lebesgue measure on `ℝ × ℝ` is used. -/
theorem ae_shift_preimage_sub_snd {A B : Set (ℝ × ℝ)} {h : ℝ} {Q : ℝ × ℝ → Prop}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hQ : ∀ᵐ q ∂(MeasureTheory.volume.restrict A), Q q)
    (hmap : ∀ q ∈ B, (q.1, q.2 - h) ∈ A) :
    ∀ᵐ q ∂(MeasureTheory.volume.restrict B), Q (q.1, q.2 - h) := by
  rw [MeasureTheory.ae_iff]
  have hA0 : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ({q : ℝ × ℝ | ¬ Q q} ∩ A) = 0 := by
    rw [← MeasureTheory.Measure.restrict_apply' hAm]
    exact MeasureTheory.ae_iff.mp hQ
  rw [MeasureTheory.Measure.restrict_apply' hBm]
  have hpre : ((fun q : ℝ × ℝ => (q.1, q.2 - h)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))
      = ((fun q : ℝ × ℝ => (0, -h) + q) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A)) := by
    rw [show (fun q : ℝ × ℝ => (q.1, q.2 - h)) = (fun q : ℝ × ℝ => (0, -h) + q) from by
      funext q
      ext <;> simp [sub_eq_add_neg, add_comm]]
  refine MeasureTheory.measure_mono_null
    (t := ((fun q : ℝ × ℝ => (q.1, q.2 - h)) ⁻¹' ({q : ℝ × ℝ | ¬ Q q} ∩ A))) ?_ ?_
  · rintro q ⟨hq1, hq2⟩
    exact ⟨hq1, hmap q hq2⟩
  · rw [hpre, MeasureTheory.measure_preimage_add]
    exact hA0

end Work.FTS.StrongEps.LocUnif
