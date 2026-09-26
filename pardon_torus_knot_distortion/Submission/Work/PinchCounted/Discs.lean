import Submission.Work.PinchCounted.Main
import Submission.Work.BoxShrink.PinchOff.Laminar

/-!
# The counted form from a laminar covering of the slice — without the planar input

The sibling chapter `Work.BoxShrink.PinchOff` proves Pardon's Lemma 3 conclusion whenever the slice
is covered by the interiors of a finite *laminar* family of embedded discs of the surface, each
inside the box (`Work.BoxShrink.PinchOff.SliceDiscCovering`,
`Work.BoxShrink.PinchOff.bubbleHalf_of_sliceDiscCovering`), and uses it for the end-to-end statement
`Work.BoxShrink.PinchOff.pardon_torus_knot_distortion_of_sliceDiscCovering` — which, like every route
through `SmoothHalfS`, has to carry the *planar* innermost input
`CleansInSphere (torus ψ) (cutDisc s c σ u)` (the sibling chapter's `hdisc`), because its route
passes through the crux's `hcleanD`.

This module records that the *counted* interface of this chapter does not need that input: a covering
gives the loop transport `RegionEquivalent (halves) (boxRegion)`
(`regionEquivalent_of_sliceDiscCovering`), hence a `PinchSweep` (`pinchSweep_of_sliceDiscCovering`),
hence `Work.BoxShrink.Pinch.CountingHalf` (`countingHalf_of_sliceDiscCovering`) — and through
`Work.BoxShrink.cruxCore_of_countingHalf` the whole challenge, with **no** planar innermost input and
**no** `Equation1Input` / `BoxSliceNice`.

The counting data of the crux is still carried (it is never used beyond the ambient general
position that the sweep supplies); the point is that the *shape* of the counted interface —
`CountingHalf`, whose conclusion is reached from the pinch without passing through the slicing disc —
makes the planar input unnecessary.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **A laminar covering of the slice gives the loop transport.**  The family is pruned to a
pairwise disjoint one with the same union of interiors
(`Work.BoxShrink.PinchOff.exists_disjoint_refinement`), and
`Work.BoxShrink.PinchOff.regionEquivalent_of_slice_in_discs` transports the loops off the slice. -/
theorem regionEquivalent_of_sliceDiscCovering
    (h : Work.BoxShrink.PinchOff.SliceDiscCovering ψ s c σ u) :
    Work.SurgeryInvariance.RegionEquivalent (Work.BoxShrink.PinchOff.surface ψ)
      (PinchSweep.halves (Work.BoxShrink.PinchOff.surface ψ) s c σ u)
      (Work.BoxShrink.Core.boxRegion (Work.BoxShrink.PinchOff.surface ψ) s c σ) := by
  obtain ⟨L, hnodup, hlaminar, hsub, hslice⟩ := h
  obtain ⟨L', hL'nodup, hsub', hdisj, hcover⟩ :=
    Work.BoxShrink.PinchOff.exists_disjoint_refinement L
      (fun D : Work.SurgeryInvariance.DiscRegion (Work.BoxShrink.PinchOff.surface ψ) => D.carrier)
      (fun D => D.interior)
      (fun D _ => Work.SurgeryInvariance.DiscRegion.interior_subset_carrier D)
      hlaminar
  refine Work.BoxShrink.PinchOff.regionEquivalent_of_slice_in_discs L' hL'nodup hdisj
    (fun D hD => hsub D (hsub' D hD)) ?_
  intro x hx
  obtain ⟨D, hD, hxD⟩ := hslice x hx
  obtain ⟨D', hD', hle⟩ := hcover D hD
  exact ⟨D', hD', hle hxD⟩

/-- **A laminar covering of the slice gives Pardon's pinch with span-preserving local models.** -/
theorem pinchSweep_of_sliceDiscCovering
    (h : Work.BoxShrink.PinchOff.SliceDiscCovering ψ s c σ u) :
    Nonempty (PinchSweep (Work.BoxShrink.PinchOff.surface ψ) s c σ u) :=
  nonempty_pinchSweep_of_regionEquivalent (regionEquivalent_of_sliceDiscCovering h)

/-- **A finite family of pairwise disjoint discs inside the box whose interiors cover the slice
gives Pardon's pinch** (the disjoint form of the previous lemma). -/
theorem pinchSweep_of_slice_in_discs (L : List (Work.SurgeryInvariance.DiscRegion
      (Work.BoxShrink.PinchOff.surface ψ)))
    (hnd : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hbox : ∀ D ∈ L, D.carrier ⊆ Work.BoxShrink.PinchOff.Omega ψ s c σ)
    (hcov : ∀ x ∈ Work.BoxShrink.PinchOff.Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Nonempty (PinchSweep (Work.BoxShrink.PinchOff.surface ψ) s c σ u) :=
  nonempty_pinchSweep_of_regionEquivalent
    (Work.BoxShrink.PinchOff.regionEquivalent_of_slice_in_discs L hnd hdisj hbox hcov)

/-- **Pardon's Lemma 3 conclusion, in the counted form, from a laminar covering of every slice.**
The counting data of the crux is carried through untouched; the covering supplies the pinching
family. -/
theorem countingHalf_of_sliceDiscCovering
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.PinchOff.SliceDiscCovering ψ s c σ u) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_pinchSweep
      (pinchSweep_of_sliceDiscCovering (h ψ s c σ u)).some

/-- **Pardon's shrinking step from a laminar covering of every slice.** -/
theorem cruxCore_of_sliceDiscCovering
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.PinchOff.SliceDiscCovering ψ s c σ u) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_sliceDiscCovering h)

/-- **Pardon's theorem from a laminar covering of every slice and his cut-and-paste** — with no
planar innermost input, no `Equation1Input` and no `BoxSliceNice`, and with the conclusion of this
chapter's counted interface.  (Compare
`Work.BoxShrink.PinchOff.pardon_torus_knot_distortion_of_sliceDiscCovering`, whose route through the
crux's `hcleanD` carries the planar input.) -/
theorem pardon_torus_knot_distortion_of_sliceDiscCovering
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.PinchOff.SliceDiscCovering ψ s c σ u) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_sliceDiscCovering h)⟩

end

end Work.PinchCounted
