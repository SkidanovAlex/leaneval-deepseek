import Submission.Work.BoxShrink.Bubble.Neck
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential

/-!
# The disc route to the pinch, and the span-invariance of a `2`-surgery

This file records the sharpest *geometric* way of producing the input of Pardon's double bubble
(`Work.BoxShrink.Bubble.NeckComponent`, which already gives the family through
`Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent`): an embedded disc of the surface
containing the slice.

## Why a disc

A `2`-surgery can only add or remove a piece which is **clopen in the region** (`Obstruction.lean`),
so the piece by which the region changes at the pinch has to be at the same time

* open in the surface (it is a union of trajectories of the pinch), and
* closed in the region (its complement in the region is what survives the pinch).

The piece which Pardon's pinch removes *is* the trace of the flat disc of the plane, so the natural
candidate is the interior of an embedded disc `D` of the surface: an embedded disc is open in the
surface (`DiscRegion.open_interior'`), carries no essential loop
(`Work.SurgeryInvariance.DiscRegion.not_isEssential`, recorded here as
`windingSpan_interior_discRegion`), and — when it contains the whole slice and lies in the region —
turns the region into the disjoint union of the two half-regions and `D.interior`
(`nonempty_neckComponent_of_sliceDisc`).

## The span-invariance of a `2`-surgery

`surgeryStepZero_windingSpan_eq` records that a `SurgeryStepZero` does not change the winding span.
It is the span-level companion of `Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero`
(which needs the two regions to be nonempty): a single `2`-surgery is span-neutral **always**, and
loop-neutral as soon as the regions are nonempty.  In particular the *span-level* content of
`Work.BoxShrink.Core.BubbleSweep` is available with no extra hypothesis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The span of an embedded disc -/

/-- **The interior of an embedded disc of the surface carries no essential loop.** -/
theorem windingSpan_interior_discRegion (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact Work.SurgeryInvariance.DiscRegion.not_isEssential D γ
    (fun t => D.interior_subset_carrier (hγ t)) hess

/-! ## The span-invariance of a single `2`-surgery -/

/-- **A `SurgeryStepZero` does not change the winding span.**  The changed piece `Z` is open in the
surface with `WindingSpan P Z = ⊥`, and the two regions are disjoint open pieces whose union is the
other one; hence every curve of either region lies in the other region or in `Z`
(`Work.SurgeryInvariance.Span.curve_subset_of_union`), so the two spans are contained in each
other (`Work.SurgeryInvariance.Span.le_sup_of_splits`). -/
theorem surgeryStepZero_windingSpan_eq {A A' : Set R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P A A') :
    Work.SurgeryInvariance.WindingSpan P A = Work.SurgeryInvariance.WindingSpan P A' := by
  obtain ⟨Z, hZ, hAopen, hA'open, hZopen, hcase⟩ := h
  rcases hcase with ⟨hAsub, hdisj⟩ | ⟨hA'sub, hdisj⟩
  · -- `A = A' ∪ Z`
    have hle : Work.SurgeryInvariance.WindingSpan P A ≤
        Work.SurgeryInvariance.WindingSpan P A' := by
      refine Work.SurgeryInvariance.Span.le_sup_of_splits (P := P) ?_ hZ
      intro γ hγ
      exact Work.SurgeryInvariance.Span.curve_subset_of_union hA'open hZopen hdisj γ
        (fun t => hAsub ▸ hγ t)
    have hge : Work.SurgeryInvariance.WindingSpan P A' ≤
        Work.SurgeryInvariance.WindingSpan P A :=
      Work.SurgeryInvariance.WindingSpan_mono P (hAsub ▸ Set.subset_union_left)
    exact le_antisymm hle hge
  · -- `A' = A ∪ Z`
    have hle : Work.SurgeryInvariance.WindingSpan P A' ≤
        Work.SurgeryInvariance.WindingSpan P A := by
      refine Work.SurgeryInvariance.Span.le_sup_of_splits (P := P) ?_ hZ
      intro γ hγ
      exact Work.SurgeryInvariance.Span.curve_subset_of_union hAopen hZopen hdisj γ
        (fun t => hA'sub ▸ hγ t)
    have hge : Work.SurgeryInvariance.WindingSpan P A ≤
        Work.SurgeryInvariance.WindingSpan P A' :=
      Work.SurgeryInvariance.WindingSpan_mono P (hA'sub ▸ Set.subset_union_left)
    exact le_antisymm hge hle

/-! ## The disc route to a neck component -/

/-- **A neck component from an embedded disc containing the slice.**

If `D` is an embedded disc of the surface whose interior contains the slice, lies in the region
inside the box, and whose complement in the region is open in the surface, then `D.interior` is a
neck component: it is open in the surface, its complement in the region is open, it contains the
slice, and it carries no essential loop.  The complement condition is the requirement that the
disc does not accumulate on the region from inside — for the disc which Pardon's pinch removes the
complement is the two half-regions. -/
theorem nonempty_neckComponent_of_sliceDisc {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior)
    (hsub : D.interior ⊆ Work.BoxShrink.Core.boxRegion P s c σ)
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.boxRegion P s c σ \ D.interior)) :
    Nonempty (NeckComponent P s c σ u) :=
  ⟨{ C := D.interior
     subset := hsub
     slice_subset := hslice
     open' := D.open_interior'
     closed' := hopen
     span := windingSpan_interior_discRegion D }⟩

/-- **The disc datum** for a box/plane configuration: an embedded disc of the surface whose
interior contains the slice, lies in the region inside the box, and whose complement in the region
is open in the surface.  This is the *geometric* form of Pardon's pinch: the sphere `∂PBox s c σ`
is pinched along the disc, and `D` is the disc which is *removed* at the pinching parameter. -/
def SliceDiscData (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ D : Work.SurgeryInvariance.DiscRegion P,
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior ∧
      D.interior ⊆ Work.BoxShrink.Core.boxRegion P s c σ ∧
      Work.SurgeryInvariance.IsOpenInCarrier P
        (Work.BoxShrink.Core.boxRegion P s c σ \ D.interior)

/-- **The disc datum gives the neck component, hence the family.** -/
theorem nonempty_neckComponent_of_sliceDiscData {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SliceDiscData P s c σ u) : Nonempty (NeckComponent P s c σ u) := by
  obtain ⟨D, h1, h2, h3⟩ := h
  exact nonempty_neckComponent_of_sliceDisc D h1 h2 h3

/-- **The field `bubble` of `Work.BoxShrink.Core.BubbleInput` from the disc datum.** -/
noncomputable def bubbleSweep_of_sliceDiscData {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SliceDiscData P s c σ u) : Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubbleSweep_of_neckComponent (Classical.choice (nonempty_neckComponent_of_sliceDiscData h))

/-- **The field, from the disc datum for every configuration.** -/
noncomputable def bubble_of_sliceDiscAll
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceDiscData P s c σ u) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P s c σ u _ _ => bubbleSweep_of_sliceDiscData (h P s c σ u)

end

end Work.BoxShrink.Bubble
