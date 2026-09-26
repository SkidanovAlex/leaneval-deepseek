import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.InnermostDisk.Defs
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.exists_closedCurve_sdiff_carrier_of_discRegion

namespace Work.BoxShrink.PinchOff

/-- **Removing the closed disc of a `DiscRegion` from a region open in the carrier which contains
its boundary circle does not increase the winding span.**

This is the span-level form of the disc push-off
`Work.BoxShrink.PinchOff.exists_closedCurve_sdiff_carrier_of_discRegion`: every loop of `X` is
matched, at the level of winding vectors, by a loop of `X \ D.carrier`, so every generator of
`WindingSpan P X` lies in `WindingSpan P (X \ D.carrier)`. -/
theorem windingSpan_le_sdiff_carrier_of_discRegion {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) (hsub : D.boundary ⊆ X) :
    Work.SurgeryInvariance.WindingSpan P X ≤
      Work.SurgeryInvariance.WindingSpan P (X \ D.carrier) := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨δ, hδ, rfl⟩
  obtain ⟨δ', hδ', hw⟩ := exists_closedCurve_sdiff_carrier_of_discRegion D hX hsub δ hδ
  rw [← hw]
  exact Submodule.subset_span ⟨δ', hδ', rfl⟩

/-- **Removing an inessential simple closed curve does not change the winding span.**  Let `P` be a
parametrised torus, `γ` a simple closed curve of `P` which is inessential (equivalently, by
`Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential`, bounds a disc of the surface), and
`X` a region of the surface, open in the carrier, containing the image of `γ`.  Then the winding
span of `X` equals the winding span of `X` with the image of `γ` removed.

`≤` is monotonicity (`WindingSpan_mono`); the content is `≥`: every winding vector realised by a
closed curve of `X` is realised by one avoiding the image of `γ`.  Since `[γ] = 0 ∈ H₁(F)` and `X`
is open in the carrier, `X` contains a full neighbourhood of `γ`; a curve of `X` meeting `γ` can be
rerouted along a parallel of `γ`, inside that neighbourhood, to a curve of `X \ range γ` with the
same winding vector.  This is the "peeling" statement behind Pardon's pinch when the trace of the
cutting plane consists of circles only: each trace circle is inessential by `hZ`, and the trace can
be removed one circle at a time without changing the winding span of the region inside the box. -/
theorem windingSpan_sdiff_range_eq_of_not_isEssential {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {γ : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : ∀ t : ℝ, γ t ∈ X) :
    Work.SurgeryInvariance.WindingSpan P X =
      Work.SurgeryInvariance.WindingSpan P (X \ Set.range γ.γ) := by
  obtain ⟨D, hD⟩ := exists_discRegion_of_not_isEssential γ hsimple hiness
  have hsubD : D.boundary ⊆ X := by
    rw [hD]
    rintro x ⟨t, rfl⟩
    exact hsub t
  refine le_antisymm ?_ ?_
  · refine le_trans (windingSpan_le_sdiff_carrier_of_discRegion D hX hsubD)
      (Work.SurgeryInvariance.WindingSpan_mono P ?_)
    intro x hx
    exact ⟨hx.1, fun hxr => hx.2 (Work.SurgeryInvariance.DiscRegion.boundary_subset_carrier D
      (hD.symm ▸ hxr))⟩
  · exact Work.SurgeryInvariance.WindingSpan_mono P Set.sdiff_subset

end Work.BoxShrink.PinchOff
