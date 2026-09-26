import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent

/-!
# The double bubble from a neck component

`Work.BoxShrink.Bubble.NeckComponent P s c σ u` is Pardon's *neck*: a piece `C` of the region
inside the box, **clopen in the region** (open in the surface, with `boxRegion ∖ C` open as well),
containing the slice and carrying no essential loop.  It is what a `2`-surgery can remove
(`Obstruction.lean`: a `SurgeryStepZero` only ever adds or removes a piece which is clopen in the
region), and it is the shape of Pardon's pinch (the collar of the slice, cut out along curves lying
on the pinching sphere).

`Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent` proves that a neck component gives
Pardon's family, by the two-step sweep

  `boxRegion`  --[remove `C`]-->  `boxRegion ∖ C`  --[add `C ∩ (upper ∪ lower)`]-->  `upper ∪ lower`,

in which both changed pieces have vanishing winding span, and the middle region is
`boxRegion ∖ C ⊆ upperRegion ∪ lowerRegion` because `sliceRegion ⊆ C`.  This file exposes it in the
shape of the field `BubbleInput.bubble`, and records the instance `span boxRegion = ⊥`.

**Caveat (why this is not yet the field).**  `C` has to be clopen in `boxRegion`, so if the region
inside the box is *connected* and the slice is not empty, `C` must be the whole region and the
hypothesis forces `WindingSpan P boxRegion = ⊥` — which is the degenerate case already covered by
`bubble_of_zero_span`.  The neck route therefore covers exactly the configurations in which the
region inside the box is disconnected with the slice lying in a zero-span component.  For a
connected region, the family `SweepLoops` must contain a genuine `RegionEquivalent` transport (the
push-off, `SlicePushOff`), because no `2`-surgery can remove a slice point from a preconnected
region (`Obstruction.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The double-bubble family from a neck component.** -/
noncomputable def bubbleSweep_of_neckComponent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : NeckComponent P s c σ u) : Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  Classical.choice (Neck.bubbleSweep_of_neckComponent N)

/-- **The field `bubble` of `Work.BoxShrink.Core.BubbleInput` from a global neck input.** -/
noncomputable def bubble_of_neckAll
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Nonempty (NeckComponent P s c σ u)) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P s c σ u _ hZ => bubbleSweep_of_neckComponent (Classical.choice (h P s c σ u hZ))

/-- **Non-vacuity of the neck route**: if the whole region inside the box carries no essential loop
then it is itself a neck component. -/
theorem nonempty_neckComponent_of_span_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥) :
    Nonempty (NeckComponent P s c σ u) := by
  refine ⟨{ C := Work.BoxShrink.Core.boxRegion P s c σ
            subset := subset_rfl
            slice_subset := Work.BoxShrink.Core.sliceRegion_subset P s c σ u
            open' := Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ
            closed' := by
              rw [Set.diff_self]
              show IsOpen (Subtype.val ⁻¹' (∅ : Set R3) : Set P.carrier)
              simp
            span := h }⟩

end

end Work.BoxShrink.Bubble
