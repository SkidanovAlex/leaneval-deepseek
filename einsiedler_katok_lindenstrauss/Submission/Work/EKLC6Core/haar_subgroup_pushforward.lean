import Mathlib
import Submission.Work.EKLC6Core.HaarSetup

namespace Work.EKLC6Core

open MeasureTheory Topology

/-- The pushforward of a Haar measure on a closed subgroup `H ≤ SL₃(ℝ)`:
it is carried by `H`, is invariant under left translation by elements of `H`,
is positive on nonempty relatively open subsets of `H`, and finite on compacts. -/
theorem haar_subgroup_pushforward {H : Subgroup Work.EKLContract.SL3}
    (hH : IsClosed (H : Set Work.EKLContract.SL3))
    (μ : MeasureTheory.Measure H) [MeasureTheory.Measure.IsHaarMeasure μ] :
    (μ.map (Subtype.val : H → Work.EKLContract.SL3)) ((H : Set Work.EKLContract.SL3))ᶜ = 0 ∧
    (∀ u : Work.EKLContract.SL3, u ∈ H → ∀ s : Set Work.EKLContract.SL3,
      s ⊆ (H : Set Work.EKLContract.SL3) → MeasurableSet s →
      (μ.map (Subtype.val : H → Work.EKLContract.SL3)) ((fun g => u * g) '' s)
        = (μ.map (Subtype.val : H → Work.EKLContract.SL3)) s) ∧
    (∀ s : Set Work.EKLContract.SL3, IsOpen s →
      s ⊆ (H : Set Work.EKLContract.SL3) → s.Nonempty →
      0 < (μ.map (Subtype.val : H → Work.EKLContract.SL3)) s) ∧
    (∀ K : Set Work.EKLContract.SL3, IsCompact K →
      (μ.map (Subtype.val : H → Work.EKLContract.SL3)) K ≠ ⊤) := by
  have hmeas : MeasurableSet (H : Set Work.EKLContract.SL3) := hH.measurableSet
  have hemb : MeasurableEmbedding
      (Subtype.val : H → Work.EKLContract.SL3) := MeasurableEmbedding.subtype_coe hmeas
  -- evaluating the pushforward on an arbitrary set of the ambient group
  have hmap : ∀ s : Set Work.EKLContract.SL3,
      (μ.map (Subtype.val : H → Work.EKLContract.SL3)) s
        = μ (Subtype.val ⁻¹' s) := fun s => hemb.map_apply μ s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmap]
    rw [subtype_preimage_compl]
    simp
  · intro u hu s _ _
    rw [hmap, subtype_preimage_mul_left_image hu s, hmap]
    exact measure_preimage_mul μ (⟨u, hu⟩ : H)⁻¹ _
  · intro s hs hsub hsne
    rw [hmap]
    refine IsOpen.measure_pos μ (hs.preimage continuous_subtype_val) ?_
    obtain ⟨x, hx⟩ := hsne
    exact ⟨⟨x, hsub hx⟩, hx⟩
  · intro K hK
    rw [hmap]
    exact (IsCompact.measure_lt_top (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK)).ne

end Work.EKLC6Core
