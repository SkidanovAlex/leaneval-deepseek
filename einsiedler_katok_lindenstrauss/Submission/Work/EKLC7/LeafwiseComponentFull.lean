import Mathlib
import Submission.Work.EKLC7.LeafwiseInvariantFull
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.leafwise_exists
import Submission.Work.EKLRelCross.leafwise_crossSection
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.leafwise_unique
import Submission.Work.EKLRelCross.leafwise_propor
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLRelCross.leafwise_entropy_cs
import Submission.Work.EKLRelCross.leafwise_ergodic

/-!
# `Work.EKLC7.P_Leafwise_proved` — component C5 (`P_Leafwise`) unconditionally

The frozen component C5, `Work.EKLContract.P_Leafwise`, is assembled in
`Work.EKLRelCross.leafwise_component : P_X3 → P_Leafwise` from the clause lemmas
`leafwise_exists`/`unique`/`crossSection`/`invariant`/`propor`/`luzin`/`acovariant`/`ergodic`/
`entropy_cs`.  All of those are proved except the `(U4)` clause `leafwise_invariant`, whose forward
direction (`IsUInvariant μ U →` a.e. right-invariance) is proved here as
`Work.EKLC7.leafwise_invariant_full` (`Submission/Work/EKLC7/LeafwiseInvariantFull.lean`).

This file is that same assembly with `leafwise_invariant_full` in place of the stubbed
`leafwise_invariant`, so it is a sorry-free proof of `P_X3 → P_Leafwise`; a client whose
`prove_Leafwise : P_Leafwise` is wired as `leafwise_component prove_X3` can replace it by
`Work.EKLC7.P_Leafwise_proved prove_X3`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC7

/-- **C5 (frozen), unconditionally**: `P_X3 → P_Leafwise`.  Same assembly as
`Work.EKLRelCross.leafwise_component`, with the `(U4)` clause supplied by
`Work.EKLC7.leafwise_invariant_full`. -/
theorem P_Leafwise_proved : Work.EKLContract.P_X3 → Work.EKLContract.P_Leafwise := by
  intro h2 μ hμ U hU t0 ht0 hcontr
  refine ⟨Work.EKLRelCross.leafwise_exists h2 μ U hU t0 ht0 hcontr, ?_⟩
  intro ν X' hL
  exact ⟨Work.EKLRelCross.leafwise_unique h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.ae_free_orbit h2 μ U hU t0 ht0 hcontr,
         Work.EKLRelCross.leafwise_crossSection h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLC7.leafwise_invariant_full h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.leafwise_propor h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.leafwise_luzin h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.leafwise_acovariant h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.leafwise_ergodic h2 μ U hU t0 ht0 hcontr ν X' hL,
         Work.EKLRelCross.leafwise_entropy_cs h2 μ U hU t0 ht0 hcontr ν X' hL⟩

end Work.EKLC7
