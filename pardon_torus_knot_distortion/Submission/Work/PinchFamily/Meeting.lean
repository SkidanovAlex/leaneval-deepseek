import Submission.Work.PinchFamily.Crosslink
import Submission.Work.PinchFamily.CollarFamily

/-!
# The residual, in its sharpest spelling: only the loops that meet the slice matter

`RegionPushOff = RegionEquivalent P halves box` has one trivial direction (the two half-regions lie
in the box region, so their loops are their own matches).  The content is therefore exactly:

> every loop of the surface inside the box region **that meets the slice trace** has a companion in
> the two half-regions with the same winding vector.

A loop of the box region that avoids the slice trace already lies in one of the two half-regions
(`boxRegion_eq_union`), so it is its own match.  This is the sharpest spelling of the residual: no
statement about the loops that avoid the slice, no family, no collar, no sphere.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The push-off is equivalent to the matching of the loops that meet the slice.** -/
theorem regionPushOff_iff_meeting {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    RegionPushOff P s c σ u ↔
      (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ box P s c σ) →
        (∃ t : ℝ, γ t ∈ slice P s c σ u) →
        ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ halves P s c σ u) ∧
          Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) := by
  constructor
  · intro h γ hγ _
    exact h.2 γ hγ
  · intro h
    refine ⟨fun γ hγ => ⟨γ, ?_, rfl⟩, fun γ hγ => ?_⟩
    · intro t
      exact Set.union_subset (Work.BoxShrink.Core.upperRegion_subset P s c σ u)
        (Work.BoxShrink.Core.lowerRegion_subset P s c σ u) (hγ t)
    · by_cases hmeet : ∃ t : ℝ, γ t ∈ slice P s c σ u
      · exact h γ hγ hmeet
      · have hmeet' : ∀ t : ℝ, γ t ∉ slice P s c σ u := fun t ht => hmeet ⟨t, ht⟩
        refine ⟨γ, fun t => ?_, rfl⟩
        by_contra hnot
        have hslice : γ t ∈ slice P s c σ u := by
          rcases Work.BoxShrink.Core.mem_boxRegion.mp (hγ t) with ⟨hyc, hyb⟩
          rcases lt_trichotomy (γ t (σ 2)) (c (σ 2) + u) with hlt | heq | hgt
          · exact absurd (Set.mem_union_right _
              (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, hlt⟩)) hnot
          · exact Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hyc, hyb, heq⟩
          · exact absurd (Set.mem_union_left _
              (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, hgt⟩)) hnot
        exact hmeet' t hslice

/-- **The residual in its sharpest spelling**: only the loops of the box region which meet the
slice trace have to be pushed off. -/
def PinchMeeting : Prop :=
  Residual fun P _β s c σ u =>
    ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ box P s c σ) →
      (∃ t : ℝ, γ t ∈ slice P s c σ u) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ halves P s c σ u) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ

/-- The push-off residual gives the meeting residual. -/
theorem pinchMeeting_of_pinchTransport (h : PinchTransport) : PinchMeeting :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    (regionPushOff_iff_meeting.mp (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox
      s hrs hs hslice u hu hS hU))

/-- The meeting residual gives the push-off residual. -/
theorem pinchTransport_of_pinchMeeting (h : PinchMeeting) : PinchTransport :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    regionPushOff_iff_meeting.mpr <| (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox
      s hrs hs hslice u hu hS hU)

/-- The two spellings are the same residual. -/
theorem pinchMeeting_iff_pinchTransport : PinchMeeting ↔ PinchTransport :=
  ⟨pinchTransport_of_pinchMeeting, pinchMeeting_of_pinchTransport⟩

/-- **The meeting residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pinchMeeting (h : PinchMeeting) : Work.PinchCounted.CountedPinch :=
  countedPinch_of_pinchTransport (pinchTransport_of_pinchMeeting h)

/-- **Pardon's Lemma 3 in the counted form, from the meeting residual.** -/
theorem countingHalf_of_pinchMeeting (h : PinchMeeting) : Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_pinchTransport (pinchTransport_of_pinchMeeting h)

/-- **Pardon's theorem from the meeting residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pinchMeeting (h : PinchMeeting)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_pinchTransport (pinchTransport_of_pinchMeeting h) hpush

end

end Work.PinchFamily
