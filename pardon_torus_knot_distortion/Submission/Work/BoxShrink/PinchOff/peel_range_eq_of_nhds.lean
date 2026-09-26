import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.InnermostDisk.Defs
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.exists_outerDiscRegion
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_boxRegion_le_sdiff_interior_union_boundary

/-!
# Peeling a simple inessential closed curve out of an arbitrary region

The target of this file is

`Work.BoxShrink.PinchOff.peel_range_eq_of_nhds`:

for a simple inessential closed curve `γ` of a parametrised torus `P` and a region `X` which
contains an *open-in-the-carrier* neighbourhood `N` of the image of `γ`, the winding span of `X`
equals the winding span of `X` with the image of `γ` removed.

## The argument

1. `γ` is simple and inessential, so it bounds an embedded disc `D` of the surface with
   `D.boundary = Set.range γ.γ` (`Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential`).
2. The neighbourhood hypothesis gives `D₂ : DiscRegion P` with `D.carrier ⊆ D₂.interior` and
   `D₂.boundary ⊆ N ⊆ X` (`Work.BoxShrink.PinchOff.exists_outerDiscRegion`): the disc `D` can be
   thickened outward inside `N`.
3. The disc re-route `disc_reroute_general D₂` pushes every loop of `X` out of `D₂.interior`
   (onto `D₂.boundary ⊆ N ⊆ X`); the re-routed loop lies in `X \ D.carrier` (because
   `D.carrier ⊆ D₂.interior` is disjoint from `D₂.boundary`) and has, by homotopy invariance
   (`Work.SurgeryInvariance.WindingOf.homotopic_eq`), the same winding vector.  Hence every
   generator of `WindingSpan P X` lies in `WindingSpan P (X \ D.carrier)`, and, since
   `X \ D.carrier ⊆ X \ Set.range γ.γ`, also in `WindingSpan P (X \ Set.range γ.γ)`.
4. The reverse inclusion is monotonicity (`WindingSpan_mono`).
-/

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The interior and the boundary of an embedded disc are disjoint (they are the images under the
injective parametrisation of the open unit ball and of the unit circle). -/
theorem discRegion_disjoint_interior_boundary' {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : Disjoint D.interior D.boundary := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, hzx⟩ ⟨z', hz', hz'x⟩
  have h : D.e z = D.e z' := by rw [hzx, hz'x]
  have hzz' : z = z' := D.inj h
  rw [hzz'] at hz
  simp only [Set.mem_ofPred_eq] at hz hz'
  linarith

/-- **The curve-level push-off for the thickened disc.**  If `X` contains an open-in-the-carrier
neighbourhood `N` of the boundary circle of an embedded disc `D`, then every loop `δ` of `X` is
homotopic, in the surface, to a loop `δ'` of `X` outside the *closed* disc `D.carrier`
(equivalently: avoiding `D.carrier`), with the same winding vector.

This is the missing input of `Work.BoxShrink.PinchOff.exists_closedCurve_sdiff_carrier_of_discRegion`
with the openness hypothesis on `X` replaced by the (weaker) neighbourhood hypothesis. -/
theorem peel_curve_sdiff_discRegion_aux {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {D : Work.SurgeryInvariance.DiscRegion P}
    (hN : ∃ N : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.SurgeryInvariance.IsOpenInCarrier P N ∧ D.boundary ⊆ N ∧ N ⊆ X)
    (δ : Work.CoreTopology.ClosedCurve P) (hδ : ∀ t : ℝ, δ t ∈ X) :
    ∃ δ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, δ' t ∈ X \ D.carrier) ∧
      Work.SurgeryInvariance.windingOf P δ' = Work.SurgeryInvariance.windingOf P δ := by
  obtain ⟨N, hNopen, hNsub, hNX⟩ := hN
  -- the outward thickening of `D` inside `N`
  obtain ⟨D₂, hD₂sub, hD₂bnd⟩ := exists_outerDiscRegion D hNopen hNsub
  -- push the loop out of `D₂.interior`
  obtain ⟨δ', hhom, hfix, hbnd⟩ :=
    Work.PinchLemma3.ClosedDiscA.disc_reroute_general D₂ δ
  refine ⟨δ', ?_, ?_⟩
  · intro t
    by_cases h : δ t ∈ D₂.interior
    · -- the excursion is placed on `D₂.boundary ⊆ N ⊆ X`, outside `D.carrier ⊆ D₂.interior`
      refine ⟨hNX (hD₂bnd (hbnd t h)), ?_⟩
      intro hc
      exact Set.disjoint_left.mp (discRegion_disjoint_interior_boundary' D₂)
        (hD₂sub hc) (hbnd t h)
    · -- the point is not moved; it was already outside `D₂.interior ⊇ D.carrier`
      refine ⟨?_, ?_⟩
      · rw [hfix t h]; exact hδ t
      · intro hc
        exact h (hfix t h ▸ hD₂sub hc)
  · exact (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm

/-- **The assembly.**  The push-off above and monotonicity give the span statement. -/
theorem peel_range_eq_of_nhds_of_peel {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} {γ : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hN : ∃ N : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P N ∧
      Set.range γ.γ ⊆ N ∧ N ⊆ X) :
    Work.SurgeryInvariance.WindingSpan P X =
      Work.SurgeryInvariance.WindingSpan P (X \ Set.range γ.γ) := by
  obtain ⟨D, hD⟩ := exists_discRegion_of_not_isEssential γ hsimple hiness
  have hND : ∃ N : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P N ∧
      D.boundary ⊆ N ∧ N ⊆ X := by
    obtain ⟨N, hNopen, hNsub, hNX⟩ := hN
    exact ⟨N, hNopen, fun x hx => hNsub (hD ▸ hx), hNX⟩
  refine le_antisymm ?_ ?_
  · -- every generator of `W X` is pushed into `X \ D.carrier ⊆ X \ range γ`
    rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan,
      Submodule.span_le]
    rintro v ⟨δ, hδ, rfl⟩
    obtain ⟨δ', hδ', hw⟩ := peel_curve_sdiff_discRegion_aux hND δ hδ
    refine Submodule.subset_span ⟨δ', ?_, ?_⟩
    · intro t
      refine ⟨(hδ' t).1, fun h => (hδ' t).2 ?_⟩
      exact Work.SurgeryInvariance.DiscRegion.boundary_subset_carrier D (hD.symm ▸ h)
    · rw [hw]
  · exact Work.SurgeryInvariance.WindingSpan_mono P Set.sdiff_subset

theorem peel_range_eq_of_nhds {P : Work.CoreTopology.ParamTorus}
    {X : Set LeanEval.KnotTheory.PardonDistortion.R3} {γ : Work.CoreTopology.ClosedCurve P}
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ)
    (hN : ∃ N : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.SurgeryInvariance.IsOpenInCarrier P N ∧ Set.range γ.γ ⊆ N ∧ N ⊆ X) :
    Work.SurgeryInvariance.WindingSpan P X =
      Work.SurgeryInvariance.WindingSpan P (X \ Set.range γ.γ) :=
  peel_range_eq_of_nhds_of_peel hsimple hiness hN

end Work.BoxShrink.PinchOff
