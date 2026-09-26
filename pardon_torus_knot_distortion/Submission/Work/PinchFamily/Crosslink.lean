import Submission.Work.PinchFamily.Reduce
import Submission.Work.BoxShrink.Pinch.Transport
import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.Instances
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_union_zeroSpan

/-!
# The push-off residual is the parent chapter's transport form

`Work.PinchFamily.RegionPushOff` is, definitionally, the parent chapter's
`Work.BoxShrink.Pinch.RegionTransport`: the relation `RegionEquivalent` between the two half-regions
and the box region.  This module records the identification and transfers the parent chapter's
instances of the transport form — which are all *proved* statements about the geometry of the
box/plane configuration — into this area, so that the family of `Work.PinchCounted.CountedPinch` is
exhibited in every one of those configurations.

This is the honest state of the residual: the transport form is *false* without restriction
(`Work.PinchFamily.not_regionPushOff_cex`), and the counted hypotheses of the crux are the extra
input that is supposed to make it true — but in the configurations below it is true outright, so
Pardon's counted Lemma 3 holds there without any appeal to the counting.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The identification -/

/-- **The push-off residual is the parent chapter's transport form**, by definition. -/
theorem regionPushOff_iff_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    RegionPushOff P s c σ u ↔ Work.BoxShrink.Pinch.RegionTransport P s c σ u := Iff.rfl

/-- The parent chapter's transport form gives the push-off residual. -/
theorem regionPushOff_of_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Pinch.RegionTransport P s c σ u) : RegionPushOff P s c σ u := h

/-- The push-off residual is the parent chapter's transport form. -/
theorem regionTransport_of_regionPushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionPushOff P s c σ u) : Work.BoxShrink.Pinch.RegionTransport P s c σ u := h

open scoped ENNReal in
/-- **The push-off residual is the parent chapter's `SlicePushOff`** in the form in which Pardon's
proof states it: every winding vector realised by a loop inside the box region is realised by a loop
of the two half-regions.  (The reverse inclusion is automatic, the halves being contained in the box
region.) -/
theorem regionPushOff_iff_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    RegionPushOff P s c σ u ↔ Work.BoxShrink.Bubble.SlicePushOff P s c σ u :=
  Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff

/-- **The residual in the parent chapter's own name**: at every counted configuration, the
transport form of `Work.BoxShrink.Pinch.RegionTransport`. -/
def CountedRegionTransport : Prop :=
  Residual fun P _β s c σ u => Work.BoxShrink.Pinch.RegionTransport P s c σ u

/-- The two spellings of the residual are the same `Prop`. -/
theorem countedRegionTransport_iff_pinchTransport :
    CountedRegionTransport ↔ PinchTransport := Iff.rfl

/-- **`CountedPinch` is the parent chapter's transport form at the counted configurations.** -/
theorem countedPinch_of_countedRegionTransport (h : CountedRegionTransport) :
    Work.PinchCounted.CountedPinch :=
  countedPinch_of_pinchTransport h

/-! ## Instances, transferred from the parent chapter -/

/-- **The family of `Work.PinchCounted.CountedPinch` exists at every configuration at which the
parent chapter's transport holds.** -/
theorem localFamilyBody_of_regionTransport (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : Work.BoxShrink.Pinch.RegionTransport P s c σ u) :
    LocalFamilyBody P β s c σ u :=
  localFamilyBody_of_regionPushOff β (regionPushOff_of_regionTransport h)

/-- **Finitely many intersection points of the cutting plane with the region inside the box.** -/
theorem regionPushOff_of_finite_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : (slice P s c σ u).Finite) : RegionPushOff P s c σ u :=
  Work.BoxShrink.Pinch.regionTransport_of_finite_slice hfin

/-- **Countably many intersection points.** -/
theorem regionPushOff_of_countable_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : (slice P s c σ u).Countable) : RegionPushOff P s c σ u :=
  Work.BoxShrink.Pinch.regionTransport_of_countable_slice hcount

/-- **The box region inside an embedded disc of the surface.** -/
theorem regionPushOff_of_boxRegion_subset_disc {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {D : Work.SurgeryInvariance.DiscRegion P} (hsub : box P s c σ ⊆ D.carrier)
    (hne : (halves P s c σ u).Nonempty) : RegionPushOff P s c σ u :=
  Work.BoxShrink.Pinch.regionTransport_of_boxRegion_subset_disc hsub hne

/-- **The box region carries no essential loop.** -/
theorem regionPushOff_of_boxRegion_span_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (box P s c σ) = ⊥)
    (hne : (halves P s c σ u).Nonempty) : RegionPushOff P s c σ u :=
  Work.BoxShrink.Pinch.regionTransport_of_windingSpan_bot hbot hne

/-- **A collar of vanishing winding span gives the push-off.**  The collar decomposition
`box = (box ∖ Z) ∪ Z` is a decomposition of the box region into two *disjoint open* pieces, so no
loop of the box region can cross between them (`Work.SurgeryInvariance.Span.curve_subset_of_union`):
a loop of the box region either lies in `box ∖ Z`, and hence in the two half-regions, or lies in `Z`
and has vanishing winding, and is matched by a constant loop of a half-region.

So the collar residuals of this area are stronger than the push-off residual, as they must be
(`pinchCollarSpan_of_pinchNeckCollar` and `countedPinchSweep_of_pinchCollarSpan`). -/
theorem regionPushOff_of_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z) (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (hx : (halves P s c σ u ∩ P.carrier).Nonempty) : RegionPushOff P s c σ u := by
  obtain ⟨a, ha, hac⟩ := hx
  refine ⟨fun γ hγ => ⟨γ, ?_, rfl⟩, fun γ hγ => ?_⟩
  · intro t
    exact Set.union_subset (Work.BoxShrink.Core.upperRegion_subset P s c σ u)
      (Work.BoxShrink.Core.lowerRegion_subset P s c σ u) (hγ t)
  · rcases Work.SurgeryInvariance.Span.curve_subset_of_union hZ.open_sdiff hZ.isOpen
      hZ.disjoint_sdiff γ (fun t => by rw [← hZ.box_eq_union]; exact hγ t) with h | h
    · exact ⟨γ, fun t => hZ.sdiff_subset_halves (h t), rfl⟩
    · have hzero : Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
        by_contra hne
        exact (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P Z).mp hspan
          ⟨γ, (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mpr hne, h⟩
      exact ⟨Work.BoxShrink.Bubble.Toolkit.constCurve P a hac, fun _ => ha,
        by rw [Work.BoxShrink.Bubble.Toolkit.windingOf_constCurve hac, hzero]⟩

/-- **Span collar gives the push-off** (whenever the two half-regions meet the surface), at the
shell level. -/
theorem pinchTransport_of_pinchCollarSpan_of_nonemptyHalves (h : PinchCollarSpan)
    (hx : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      (halves P s c σ u ∩ P.carrier).Nonempty) : PinchTransport :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨Z, hZ, hspan⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    regionPushOff_of_collar hZ hspan (hx (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **The push-off when the slice trace is open in the surface and carries no essential loop.** -/
theorem regionPushOff_of_sliceRegion_open {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (slice P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (slice P s c σ u))
    (hne : (halves P s c σ u).Nonempty) : RegionPushOff P s c σ u :=
  (Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff).mpr
    (Work.BoxShrink.Bubble.slicePushOff_of_sliceOpen hopen hZ hne)

/-- **The push-off is only about the loops that meet the slice**: if every loop of the box region
meeting the slice trace has a companion in the two half-regions with the same winding vector, then
the push-off holds.  This is the sharpest form of the residual that the parent chapter isolates. -/
theorem regionPushOff_of_meeting {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ box P s c σ) → (∃ t : ℝ, γ t ∈ slice P s c σ u) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ halves P s c σ u) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) :
    RegionPushOff P s c σ u :=
  (Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff).mpr
    (Work.BoxShrink.Bubble.slicePushOff_of_meeting h)

/-- The transfer at the level of the family, for a finite slice trace. -/
theorem localFamilyBody_of_finite_slice (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (hfin : (slice P s c σ u).Finite) :
    LocalFamilyBody P β s c σ u :=
  exists_region_of_regionPushOff β (regionPushOff_of_finite_slice hfin)

/-- The transfer at the level of the family, for a slice trace inside an embedded disc. -/
theorem localFamilyBody_of_boxRegion_subset_disc (β : Work.CoreTopology.ClosedCurve P) {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (hsub : box P s c σ ⊆ D.carrier) (hne : (halves P s c σ u).Nonempty) :
    LocalFamilyBody P β s c σ u :=
  exists_region_of_regionPushOff β (regionPushOff_of_boxRegion_subset_disc hsub hne)

end

end Work.PinchFamily
