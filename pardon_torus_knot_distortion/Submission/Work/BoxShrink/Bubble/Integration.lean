import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Core.Crux

/-!
# The double bubble inside the reduction of the crux

This file shows how the chapter plugs into the reduction of the challenge: with the isolated input
`Work.BoxShrink.Bubble.SlicePushOff` (for every configuration whose slicing plane carries no
essential loop) one gets

* the field `bubble` of `Work.BoxShrink.Core.BubbleInput`, in the exact shape of the structure's
  field (`bubbleFrom`), and
* hence `Work.BoxShrink.CruxStatement` — Pardon's shrinking step — together with the two classical
  inputs of `Work.BoxShrink.crux` and the planar innermost-disc input at the slicing disc (the
  field `cleansInDisc` of `BubbleInput`, the subject of the sibling subproject).

The content of `SlicePushOff` is documented in `README.md`: it is the push-off of the loops of the
region inside the box off the slicing plane, i.e. Pardon's pinch at the level of loops.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The field `bubble` of `Work.BoxShrink.Core.BubbleInput`**, given the isolated geometric input
for every configuration whose slicing plane carries no essential loop. -/
noncomputable def bubbleFrom
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      SlicePushOff P s c σ u) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_pushOffAll h

/-- **Pardon's shrinking step from the push-off.**  From the isolated input, the planar
innermost-disc input at the slicing disc (`BubbleInput.cleansInDisc`), and the two classical inputs
of `Work.BoxShrink.crux` (the cut-and-paste at the surface, and the almost-everywhere general
position of the box norm), one obtains `Work.BoxShrink.CruxStatement` for all `p q`. -/
theorem crux_of_pushOffAll
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      SlicePushOff P s c σ u)
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  Work.BoxShrink.Core.crux ⟨hdisc, bubble_of_pushOffAll h⟩ hclean hae

end

end Work.BoxShrink.Bubble
