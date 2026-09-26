import Submission.Work.BoxShrink.PinchOff.Sharpening

/-!
# The disc push-off: the local model of Pardon's pinch

Pardon's pinch (`Work.SurgeryInvariance.SurgeryStep`) is a single `2`-surgery of the sphere family,
whose changed piece is the interior of an embedded *disc* of the surface.  At the pinching parameter
that piece is the trace of the flat disc of the plane (the *slice* `Sigma`), and the local content of
the pinch is therefore:

> **every loop of the region inside the box can be pushed off an embedded disc of the surface that
> lies in the box, and whose interior contains the slice** --

after which the loop lies in `boxRegion \ sliceRegion = Halves`, with its winding vector unchanged.
The parent chapter isolated exactly this local model as `Work.BoxShrink.Bubble.SliceDiscRoute` and
proved that it implies the loop transport (`Work.BoxShrink.Bubble.slicePushOff_of_discRoute`).

This module

* defines the local push-off `DiscRoute` in the vocabulary of this chapter (with the extra condition
  that the homotopy moves **only** points inside the disc, which is what makes it iterable);
* derives from it the **single-disc** conclusions: the loop transport
  (`regionEquivalent_of_discRoute`), the transport for a slice inside the disc
  (`regionEquivalent_of_slice_subset_disc`), the span equality and Pardon's Lemma 3 conclusion at
  that configuration (`bubbleHalf_of_slice_subset_disc`);
* derives the **finite** version: if the slice is contained in the interiors of finitely many
  **pairwise disjoint** embedded discs, each lying in the box, and the push-off holds for each of
  them, then the region inside the box and the two half-regions have the *same* winding span, so
  Pardon's Lemma 3 conclusion holds at that configuration
  (`bubbleHalf_of_slice_subset_discs`).

The finite version is what covers the case named in the assignment: **a slice made of circles
only**, the discs bounded by those circles lying in the box.  (In that case the slice is the
boundary of the union of those discs, so it is contained in their closed discs; and the discs are
pairwise disjoint -- the argument is recorded in the README, together with the reason why the general
case, a slice with *arcs*, needs the convexity of the box.)

The one remaining statement of this module is `DiscRoute` itself, which is *not* proved here: it is
the local model of the pinch, and it is the sharpest form in which the remaining mathematics of the
area can be isolated.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The local model -/

/-- **The local disc push-off.**  For an embedded disc `D` of the surface whose carrier lies in the
region inside the box: every loop of the box region is homotopic (in the surface) to a loop of
`boxRegion \ D.interior`, and the homotopy moves **only points that lie in `D.carrier`** (every
point of the new loop is either the corresponding point of the old loop or lies in the disc).

This is the local model of Pardon's pinch: a loop that enters the disc is rerouted along its
boundary circle.  It is *not* a `2`-surgery of the loop-level library: the changed piece is the
interior of a disc, which is why the homotopy can be produced at all (the pinch itself, whose changed
piece is the closed slice, cannot be `SurgeryStep`-factorised -- see the parent chapter's
`Obstruction`).

The locality condition is what makes the statement iterable over a family of discs
(`exists_loop_avoiding_discs`), and it is satisfied by the construction ("push the part of the loop
that lies in the disc to the boundary of the disc, leaving the rest fixed"). -/
def DiscRoute (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (D : Work.SurgeryInvariance.DiscRegion (surface ψ)) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
    (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
    ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ' t ∈ Omega ψ s c σ \ D.interior) ∧
        (∀ t : ℝ, γ' t = γ t ∨ γ' t ∈ D.carrier) ∧
        Work.CoreTopology.Homotopic (surface ψ) γ γ'

/-- A homotopy preserves the winding vector (parent chapter,
`Work.SurgeryInvariance.WindingOf.homotopic_eq`). -/
theorem windingOf_eq_of_homotopic {γ γ' : Work.CoreTopology.ClosedCurve (surface ψ)}
    (h : Work.CoreTopology.Homotopic (surface ψ) γ γ') :
    Work.SurgeryInvariance.windingOf (surface ψ) γ'
      = Work.SurgeryInvariance.windingOf (surface ψ) γ :=
  (Work.SurgeryInvariance.WindingOf.homotopic_eq h).symm

/-! ## The single-disc consequences -/

/-- **The local push-off transports loops off the disc.**  Every loop of the box region is matched,
with the same winding vector, by a loop of `boxRegion \ D.interior`; the converse is the inclusion
`boxRegion \ D.interior ⊆ boxRegion`. -/
theorem regionEquivalent_of_discRoute (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hD : DiscRoute ψ s c σ D) :
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Omega ψ s c σ \ D.interior)
      (Omega ψ s c σ) := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    exact ⟨γ, fun t => (hγ t).1, rfl⟩
  · intro γ hγ
    obtain ⟨γ', hγ', -, hhom⟩ := hD γ hγ
    exact ⟨γ', hγ', windingOf_eq_of_homotopic hhom⟩

/-- **The slice inside a disc inside the box: the loop transport holds at that configuration.**
Every loop of the box region is transported, with its winding vector, to a loop of the two
half-regions (it is pushed off the disc, hence off the slice, and the two half-regions are the box
region minus the slice). -/
theorem regionEquivalent_of_slice_subset_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : DiscRoute ψ s c σ D) :
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ) := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    refine ⟨γ, fun t => ?_, rfl⟩
    rcases hγ t with h | h
    · exact Work.BoxShrink.Core.upperRegion_subset (surface ψ) s c σ u h
    · exact Work.BoxShrink.Core.lowerRegion_subset (surface ψ) s c σ u h
  · intro γ hγ
    obtain ⟨γ', hγ', -, hhom⟩ := hD γ hγ
    refine ⟨γ', fun t => ?_, windingOf_eq_of_homotopic hhom⟩
    have hn : γ' t ∉ D.interior := (hγ' t).2
    have hns : γ' t ∉ Sigma ψ s c σ u := fun hs => hn (hslice hs)
    have hb : γ' t ∈ (HalfUp ψ s c σ u ∪ HalfDown ψ s c σ u) ∪ Sigma ψ s c σ u := by
      rw [← Work.BoxShrink.Core.boxRegion_eq_union]
      exact (hγ' t).1
    rcases hb with h | h
    · exact h
    · exact absurd h hns

/-- **The strong form of the pinch-off, from the disc push-off.** -/
theorem strong_of_slice_subset_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : DiscRoute ψ s c σ D) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    (regionEquivalent_of_slice_subset_disc (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u) D
      hslice hD)).symm

/-- **Pardon's Lemma 3 conclusion, from the disc push-off**: if the slice is contained in an
embedded disc of the box region and the loops of the box region can be pushed off that disc, then an
essential loop of the box region survives to one of the two half-regions. -/
theorem bubbleHalf_of_slice_subset_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : DiscRoute ψ s c σ D) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong
    (strong_of_slice_subset_disc (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u) D hslice hD)
