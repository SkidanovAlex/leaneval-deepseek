import Submission.Work.BoxShrink.PinchOff.Discs
import Submission.Work.BoxShrink.PinchOff.discRoute_holds

/-!
# The disc push-off is a theorem: the configurations it discharges

`DiscPush.lean` and `Discs.lean` derived the consequences of the local disc push-off `DiscRoute`.
`discRoute_holds.lean` (delegated, and proved) supplies `DiscRoute` for **every** embedded disc of
the surface whose carrier lies in the box region.  This module therefore removes the `DiscRoute`
hypothesis from those consequences and records the resulting unconditional statements:

* `bubbleHalf_of_slice_in_disc` -- Pardon's Lemma 3 conclusion for a slice contained in the
  *interior* of an embedded disc inside the box;
* `bubbleHalf_of_slice_in_discs` -- the same for a slice covered by the interiors of finitely many
  pairwise disjoint such discs (the shape in which a slice made of *circles only* is handled, modulo
  the two elementary structural lemmas listed in `README.md` §3);
* the span forms `strong_of_slice_in_disc`, `strong_of_slice_in_discs`;
* `smoothHalfS_of_slice_in_discs` -- the *global* conditional form: if in every configuration the
  slice is covered by finitely many pairwise disjoint discs inside the box, then Pardon's Lemma 3
  holds for the smooth tori of the challenge.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## One disc -/

/-- **The loop transport for a slice contained in an embedded disc inside the box** (the local model
is a theorem now). -/
theorem regionEquivalent_of_slice_in_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : D.carrier ⊆ Omega ψ s c σ) :
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ) :=
  regionEquivalent_of_slice_subset_disc D hslice (discRoute_holds ψ s c σ D hD)

/-- **The span form, for a slice contained in an embedded disc inside the box.** -/
theorem strong_of_slice_in_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : D.carrier ⊆ Omega ψ s c σ) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  strong_of_slice_subset_disc D hslice (discRoute_holds ψ s c σ D hD)

/-- **Pardon's Lemma 3 conclusion, for a slice contained in an embedded disc inside the box.** -/
theorem bubbleHalf_of_slice_in_disc (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hslice : Sigma ψ s c σ u ⊆ D.interior) (hD : D.carrier ⊆ Omega ψ s c σ) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_slice_subset_disc D hslice (discRoute_holds ψ s c σ D hD)

/-! ## Finitely many disjoint discs -/

/-- **The loop transport, for a slice covered by finitely many pairwise disjoint discs inside the
box** (the local model is a theorem now). -/
theorem regionEquivalent_of_slice_in_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hsub : ∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.SurgeryInvariance.RegionEquivalent (surface ψ) (Halves ψ s c σ u) (Omega ψ s c σ) :=
  regionEquivalent_of_slice_subset_discs L hnodup hdisj
    (fun D hD => discRoute_holds ψ s c σ D (hsub D hD)) hslice

/-- **The span form, for a slice covered by finitely many pairwise disjoint discs inside the box.** -/
theorem strong_of_slice_in_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hsub : ∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  strong_of_slice_subset_discs L hnodup hdisj
    (fun D hD => discRoute_holds ψ s c σ D (hsub D hD)) hslice

/-- **Pardon's Lemma 3 conclusion for a slice covered by finitely many pairwise disjoint discs
inside the box.**  This is the unconditional form of the assignment's named partial target: a slice
made of *circles only*, the discs bounded by those circles lying in the box (see `README.md` §3: the
thickened discs give a laminar covering, and pruning a laminar covering by interiors to a disjoint
one is a one-line argument, which is the only place where the nested case enters). -/
theorem bubbleHalf_of_slice_in_discs
    (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) (hnodup : L.Nodup)
    (hdisj : ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier)
    (hsub : ∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ)
    (hslice : ∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_slice_subset_discs L hnodup hdisj
    (fun D hD => discRoute_holds ψ s c σ D (hsub D hD)) hslice

/-! ## The global conditional form -/

/-- **The deliverable, from the hypothesis that the slice is always carried by discs inside the
box.**  If in every configuration the slice is covered by the interiors of finitely many pairwise
disjoint embedded discs, each lying in the box region, then Pardon's Lemma 3 holds for every smooth
torus of the challenge (with both endpoint hypotheses) -- i.e. `SmoothHalfS`, hence (with Pardon's
equation (1) and the general position of the box-sphere trace) the challenge.

This isolates exactly what a "cap the slice by discs" argument would have to produce; the residual
`Key` is the statement that the box spheres and the slicing planes of the challenge never need more
than the *local* model for that. -/
theorem smoothHalfS_of_slice_in_discs
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ∃ L : List (Work.SurgeryInvariance.DiscRegion (surface ψ)), L.Nodup ∧
        (∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier) ∧
        (∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ) ∧
        (∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior)) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  fun ψ s c σ u _ _ => by
    obtain ⟨L, hnodup, hdisj, hsub, hslice⟩ := h ψ s c σ u
    exact bubbleHalf_of_slice_in_discs L hnodup hdisj hsub hslice

end

end Work.BoxShrink.PinchOff
