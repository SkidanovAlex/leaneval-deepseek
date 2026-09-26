import Submission.Work.BoxShrink.Core.Bubble.Defs
import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Corrected

/-!
# Probe: the migration of `Core/Bubble/Defs.lean` typechecks without an import cycle

This module is *not* part of the chapter's mathematical content: it is the verification of the two
patches of `MIGRATION.md`.  It shows that

* `Submission.Work.BoxShrink.Bubble.HalfDefs` can be imported by
  `Submission.Work.BoxShrink.Core.Bubble.Defs` (no cycle: `HalfDefs` only depends on
  `Work.BoxShrink.Core.Basic` and two modules of `Work.SurgeryInvariance`), and that the two
  replacement structures can be written there;
* the crux replays of `Work.BoxShrink.Bubble.Corrected` /
  `Work.BoxShrink.Bubble.PardonLocalModel` then give `Work.BoxShrink.CruxCore` from them.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

/-- **The two-line replacement of the field.**  The caller's structure with the double-bubble
field weakened to Pardon's Lemma 3 conclusion: identical to `Work.BoxShrink.Core.BubbleInput` except
that the codomain of `bubble` is `Work.BoxShrink.Bubble.BubbleHalf` instead of `BubbleSweep`. -/
structure BubbleInputWeakened where
  /-- the classical (planar) innermost-disc input at every flat disc cut out of a box by a plane -/
  cleansInDisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.InnermostDisk.CleansInSphere
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (cutDisc s c σ u)
  /-- Pardon's Lemma 3 conclusion, for every configuration whose two cuts are inessential -/
  bubble : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ),
    ¬ P.ContainsEssentialLoop (sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (sliceRegion P s c σ u) →
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u

/-- The same content as the chapter's own drop-in structure (one `abbrev` instead of the copy
above). -/
abbrev BubbleInputAlias := Work.BoxShrink.Bubble.BubbleInputHalf

/-- The crux replays of the chapter apply to the migrated structure directly. -/
theorem cruxCore_of_bubbleInputWeakened (hin : BubbleInputWeakened) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf hin.cleansInDisc hin.bubble

/-- The same, through the `abbrev`. -/
theorem cruxCore_of_bubbleInputAlias (hin : BubbleInputAlias) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.Bubble.cruxCore_of_bubbleInputHalf hin

/-- And the Pardon-faithful replacement: the field becomes `PinchDatum` (import
`Work.BoxShrink.Bubble.HalfDefs` only). -/
theorem cruxCore_of_bubbleInputPardonProbe (hin : Work.BoxShrink.Bubble.BubbleInputPardon) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.Bubble.cruxCore_of_pushOffHalf hin.cleansInDisc
    (Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput hin.bubble)

end

end Work.BoxShrink.Core
