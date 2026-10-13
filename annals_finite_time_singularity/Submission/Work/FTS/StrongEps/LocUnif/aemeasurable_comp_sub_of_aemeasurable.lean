import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.LocUnif.ae_shift_preimage_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- **A.e.-measurability transfers under a horizontal translation.**  If `f` is
a.e.-measurable on `A` and the shift `q ↦ (q.1 - h, q.2)` maps `B` into `A`, then the
composite `q ↦ f (q.1 - h, q.2)` is a.e.-measurable on `B`.

Proof: `AEMeasurable f (volume.restrict A)` unfolds to a *measurable* `g` with
`f =ᵐ[volume.restrict A] g`; the a.e. equality is transported across the shift by
`ae_shift_preimage_sub`, and `g ∘ shift` is measurable. -/
theorem aemeasurable_comp_sub_of_aemeasurable {A B : Set (ℝ × ℝ)} {h : ℝ} {β : Type*}
    [MeasurableSpace β] {f : ℝ × ℝ → β}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hmap : ∀ q ∈ B, (q.1 - h, q.2) ∈ A)
    (hf : AEMeasurable f (MeasureTheory.volume.restrict A)) :
    AEMeasurable (fun q : ℝ × ℝ => f (q.1 - h, q.2)) (MeasureTheory.volume.restrict B) := by
  obtain ⟨g, hgm, hfg⟩ := hf
  refine ⟨fun q : ℝ × ℝ => g (q.1 - h, q.2), hgm.comp ?_, ?_⟩
  · exact (measurable_fst.sub_const h).prodMk measurable_snd
  · have h := ae_shift_preimage_sub (Q := fun q => f q = g q) hAm hBm hfg hmap
    filter_upwards [h] with q hq
    exact hq

end Work.FTS.StrongEps.LocUnif
