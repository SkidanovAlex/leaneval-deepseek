import Submission.Work.BoxShrink.PinchOff.Discs
import Submission.Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice
import Submission.Work.BoxShrink.Bubble.Plane.CountableSlice
import Submission.Work.BoxShrink.Bubble.DiscRoute

/-!
# The configurations in which the residual is discharged

`Basic.lean` reduces the deliverable (`Work.BoxShrink.Pinch.SmoothHalfS`) to the residual `Key`.
This module collects the configurations in which the residual -- in its strong form
`Work.SurgeryInvariance.WindingSpan Omega = WindingSpan Halves`, which implies `Key` by
`strong_to_key` -- is *proved*, i.e. the configurations in which Pardon's Lemma 3 conclusion holds
unconditionally:

* the slice is empty (the box region *is* the union of the two halves);
* the slice is finite, or countable (the parent chapter's parameter-plane routing);
* the box region is contained in an embedded disc of the surface (every loop of it is
  inessential, so `BubbleHalf` is vacuous);
* the slice is contained in finitely many pairwise disjoint embedded discs inside the box and the
  local model `DiscRoute` holds for them (`Discs.lean`; this is the circles-only case).

Each statement is *per configuration*: a configuration satisfying one of these conditions
discharges Pardon's Lemma 3 conclusion there, without any hypothesis on the box sphere or on the
winding span of the slice.  Together with `smoothHalfS_of_key`, they give the reader the exact shape
of the remaining problem: the configurations in which the slice is a *finite union of arcs* (with
endpoints on the trace of the box sphere) and the discs bounded by the circles do *not* lie in the
box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## From the loop transport -/

/-- The parent chapter's loop transport (`SlicePushOff`) gives the strong form of the residual. -/
theorem strong_of_slicePushOff
    (h : Work.BoxShrink.Bubble.SlicePushOff (surface ψ) s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    ((Work.BoxShrink.Pinch.regionTransport_iff_slicePushOff (P := surface ψ)
      (s := s) (c := c) (σ := σ) (u := u)).mpr h)).symm

/-- The parent chapter's loop transport gives Pardon's Lemma 3 conclusion. -/
theorem bubbleHalf_of_slicePushOff
    (h : Work.BoxShrink.Bubble.SlicePushOff (surface ψ) s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong (strong_of_slicePushOff h)

/-! ## The degenerate configurations -/

/-- **The slice is empty**: the box region is already the union of the two halves. -/
theorem bubbleHalf_of_empty_slice
    (h : Sigma ψ s c σ u = ∅) : Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_slicePushOff
    (Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice (P := surface ψ)
      (s := s) (c := c) (σ := σ) (u := u) h)

/-- **The slice is finite**: the parent chapter's perturbation argument in the parameter plane. -/
theorem bubbleHalf_of_finite_slice (h : (Sigma ψ s c σ u).Finite) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_slicePushOff
    (Work.BoxShrink.Bubble.slicePushOff_of_finite_slice (P := surface ψ) (s := s) (c := c)
      (σ := σ) (u := u) h)

/-- **The slice is countable**. -/
theorem bubbleHalf_of_countable_slice (h : (Sigma ψ s c σ u).Countable) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_slicePushOff
    (Work.BoxShrink.Bubble.slicePushOff_of_countable_slice (P := surface ψ) (s := s) (c := c)
      (σ := σ) (u := u) h)

/-- **The box region is contained in an embedded disc** of the surface: every loop of it is
inessential, so the residual is vacuous. -/
theorem strong_of_boxRegion_subset_discRegion (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hsub : Omega ψ s c σ ⊆ D.carrier)
    (hne : (Halves ψ s c σ u).Nonempty) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)
      = Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    (Work.BoxShrink.Pinch.regionTransport_of_boxRegion_subset_disc (P := surface ψ)
      (s := s) (c := c) (σ := σ) (u := u) (D := D) hsub hne)).symm

/-- The same, in the form of Pardon's Lemma 3 conclusion. -/
theorem bubbleHalf_of_boxRegion_subset_discRegion (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hsub : Omega ψ s c σ ⊆ D.carrier)
    (hne : (Halves ψ s c σ u).Nonempty) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong (strong_of_boxRegion_subset_discRegion D hsub hne)

/-- **The plane misses the box region**: the two half-regions are the whole box region. -/
theorem bubbleHalf_of_halves_eq_boxRegion
    (h : Halves ψ s c σ u = Omega ψ s c σ) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u :=
  bubbleHalf_of_strong (by rw [h])

/-! ## The dictionary with the parent chapter's local model -/

/-- **The parent chapter's local model `SliceDiscRoute` follows from this chapter's `DiscRoute`**
(the two differ only in the placement of the quantifier over the loop). -/
theorem sliceDiscRoute_of_discRoute (D : Work.SurgeryInvariance.DiscRegion (surface ψ))
    (hD : DiscRoute ψ s c σ D) :
    Work.BoxShrink.Bubble.SliceDiscRoute (surface ψ) s c σ u D :=
  fun γ hγ => by
    obtain ⟨γ', hγ', -, hhom⟩ := hD γ hγ
    exact ⟨γ', hγ', hhom⟩

end

end Work.BoxShrink.PinchOff
