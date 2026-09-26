import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.BoxShrink.Bubble.Neck.neckComponent_removalStep
import Submission.Work.BoxShrink.Bubble.Neck.neckComponent_additionStep
import Submission.Work.SurgeryInvariance.Sweep.exists_sweepLoops_threeStep

/-!
# The double bubble from a neck component

`Work.BoxShrink.Bubble.NeckComponent P s c σ u` is Pardon's *neck*: a piece `C` of the region of
the surface inside the box which

* contains the slice (`sliceRegion ⊆ C`),
* lies in the region (`C ⊆ boxRegion`),
* is open in the surface, with `boxRegion ∖ C` open as well (i.e. `C` is clopen in the region),
* carries no essential loop (`WindingSpan P C = ⊥`).

`Work.BoxShrink.Bubble.Neck.bubbleSweep_of_neckComponent` proves that a neck component gives
Pardon's family, by the two-step sweep

  `boxRegion`  --[remove `C`]-->  `boxRegion ∖ C`  --[add `C ∩ (upper ∪ lower)`]-->  `upper ∪ lower`,

in which both changed pieces have vanishing winding span, and the intermediate region is
`boxRegion ∖ C ⊆ upperRegion ∪ lowerRegion` because `sliceRegion ⊆ C`.

Concretely, writing

* `B = boxRegion P s c σ` (open in the surface; `boxRegion_eq_union` gives
  `B = (upperRegion ∪ lowerRegion) ∪ sliceRegion`),
* `U = upperRegion P s c σ u ∪ lowerRegion P s c σ u` (open in the surface, being a union of the
  two open half-regions), and
* `C = N.C` (with `C ⊆ B`, `sliceRegion ⊆ C`, `WindingSpan P C = ⊥`),

the three regions of the sweep are `B`, `B ∖ C` and `U = (B ∖ C) ∪ (C ∩ U)`, so that

* `SurgeryStepZero P B (B ∖ C)` — the removal of the zero-span piece `C`
  (`B = (B ∖ C) ∪ C` since `C ⊆ B`, and `B ∖ C` is open in the surface by the field `closed'` of the
  neck component): `Work.BoxShrink.Bubble.Neck.neckComponent_removalStep`;
* `SurgeryStepZero P (B ∖ C) U` — the addition of the zero-span piece `C ∩ U`
  (`C ∩ U ⊆ C`, so `WindingSpan P (C ∩ U) = ⊥`):
  `Work.BoxShrink.Bubble.Neck.neckComponent_additionStep`.

Two consecutive `SurgeryStepZero`s make a loop-level sweep between their endpoint regions
(`Work.SurgeryInvariance.Sweep.exists_sweepLoops_threeStep`): the piecewise constant family which is
`B` for `t < 1/3`, `B ∖ C` for `1/3 ≤ t ≤ 2/3` and `U` for `2/3 < t`, with exceptional parameters
`{1/3, 2/3}`, satisfies the local models of `Work.SurgeryInvariance.SweepLoops` — no regularity of
the family in the parameter is required by that structure, so a piecewise constant family is
legitimate, and each of the two changes of region is one of the two surgeries above.  Reading the
endpoints of that sweep off (`region 0 = B = boxRegion`, `region 1 = U = upperRegion ∪ lowerRegion`)
gives the required `Work.BoxShrink.Core.BubbleSweep`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble.Neck

noncomputable section

theorem bubbleSweep_of_neckComponent
    {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : Work.BoxShrink.Bubble.NeckComponent P s c σ u) :
    Nonempty (Work.BoxShrink.Core.BubbleSweep P s c σ u) := by
  obtain ⟨S, h0, h1⟩ := Work.SurgeryInvariance.Sweep.exists_sweepLoops_threeStep
    (neckComponent_removalStep N) (neckComponent_additionStep N)
  exact ⟨{ sweep := S, zero := h0, one := h1 }⟩

end

end Work.BoxShrink.Bubble.Neck
