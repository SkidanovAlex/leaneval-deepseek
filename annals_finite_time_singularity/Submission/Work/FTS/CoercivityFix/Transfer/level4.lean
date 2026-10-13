/-# `Transfer/level4.lean` — the joint induction to level `4` (aggregator)

`Transfer/L4Step.lean` carries the single step (`stepPair`, `LevelPkg`); `Transfer/L4Main.lean`
carries `transfer_level4`, the level-`4` assembly.  This module re-exports both so that
consumers can keep importing `Submission.Work.FTS.CoercivityFix.Transfer.level4`.

## The design

Running the two inductions side by side produces, with one choice of step coefficients,

* `Assembly.CoerData2 α 4 (IP4 c… α) cc CC` — the level-4 Cauchy–Schwarz bound of `IP4`
  (the `cs` clause of the headline), and
* `Transfer.CoerDataT α 4 (IP4 c… α) cc₄ CC₄` — its coercivity clause on `CoerAdm`, i.e. the
  `coer` clause of the headline.

The coefficients `c₁ = c₁' = c₁'' = 1` are used throughout; `c₂, c₂', c₂''` are chosen small
enough to satisfy simultaneously the clean `StepSmall` and the two conditions `hs3`, `hs4` of
`stepT`.  The conditions `hs1`, `hs2` (which involve `α`) are met by taking `α` below an
explicit bound `α₂ ≪ 1`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.CoercivityFix.Transfer.L4Step
import Submission.Work.FTS.CoercivityFix.Transfer.L4Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
