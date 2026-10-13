import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.est_step_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HonGaps.estStepWeak`: the induction step of Elgindi's `prop:Hk`, in the weak class

## What the lemma says

For every `k ≥ 3`, the level-`0` estimate `TT.EllWeak0` (the paper's `prop:L2` with the
`w² sin^{-η}` weights, i.e. Steps 1--2 of `prop:H2`) together with the level-`(k-1)` estimate
`TT.EllEstUnif (k-1)` for **all** data of the weak class `TT.EllWeakPos` (with a constant that is
uniform in `α ∈ (0,1/4]`) yields the level-`k` estimate `TT.EllEstUnif k`, again with an
`α`-uniform constant: Elgindi's §"General `ℋ^k` Case" (tex 986--1008).

## Where the mathematics lives

The statement of this file is *character for character* the statement of

> `Work.FTS.EllipticEst.TT.est_step_weak` (`Submission/Work/FTS/EllipticEst/TT/est_step_weak.lean`),

which is **fully proved** in this workspace, `sorry`-free, and rests only on
`[propext, Classical.choice, Quot.sound]` (verified with `#print axioms`).  Its proof is the
assembly `TT.ESW.Pieces.EllEstUnif_step_of_pieces` (the exact splitting of `HkSq` at level `k`,
the domination of the shifted level-`(k-1)` expression, the admissibility of the radially
differentiated data `EllWeakPos_DzIter_one_shift`, and the two top angular slots: `A_top_slot_bound`
and `ESW.bSlot_bound`, the latter fed by `Prop.Rtilde.SourceLe` and the one-dimensional far-region
bound `remov.EllUnifBslot.slice_ang_gen_live`).

There is therefore nothing to re-prove: this module simply re-exports that theorem under the
`HonGaps` name, so that consumers of the "honest" (weak-hypothesis) route can obtain the induction
step without naming the `TT` module.  The re-export is *not* a cycle hazard for the current tree:
the import closure of `TT.est_step_weak` (478 modules) contains no `AngAWeak`, no `Prop/Level0`,
no `Cores/propHk_fts` and no file of this `HonGaps` directory (in particular it avoids the
duplicate-`AngAWeak.Yslice` collision), so it can be imported alongside any of them.

## Traps worth recording for a consumer

* the two moment conditions of `EllWeakPos` are demanded only for `z > 0`
  (`TT.WeakDefs.EllWeakPos`), and the induction step above consumes exactly that class;
* the dependence on `k` is via `k - 1` on `ℕ`, i.e. for `k ≥ 3` (the `k = 2` base case is the
  paper's `prop:H2`, `TT.est_two_weak`, and is *not* reachable from this lemma);
* the hypothesis `∃ C, 0 < C ∧ EllWeak0 C` is part of the *statement* of the step (the paper's
  proof of the general case re-uses the level-`0` estimate on the radially shifted data); it is
  not used by the re-exported proof term in any way the consumer must check separately.
-/

namespace Work.FTS.EllipticEst.HonGaps

/-- **Elgindi's §"General `ℋ^k` Case"** (the induction step of `prop:Hk`), in the weak hypothesis
class `TT.EllWeakPos`: for every `k ≥ 3`, the level-`0` estimate `TT.EllWeak0` together with the
level-`(k-1)` estimate `TT.EllEstUnif (k-1)` for all weak data implies the level-`k` estimate
`TT.EllEstUnif k`, with an `α`-uniform constant.

Proved as `Work.FTS.EllipticEst.TT.est_step_weak`, whose statement is identical. -/
theorem estStepWeak : ∀ k : ℕ, 3 ≤ k →
    (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) →
    (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif (k - 1) C) →
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C :=
  Work.FTS.EllipticEst.TT.est_step_weak

end Work.FTS.EllipticEst.HonGaps
