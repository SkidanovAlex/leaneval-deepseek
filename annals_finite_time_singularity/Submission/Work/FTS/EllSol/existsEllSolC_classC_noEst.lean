import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllSol.existsEllSolC_classC_of
import Submission.Work.FTS.EllipticEst.Prop.Step
import Submission.Work.FTS.EllipticEst.Dispatch.cores_level_zero
import Submission.Work.FTS.EllipticEst.Cores.levelTwo_fts
import Submission.Work.FTS.EllipticEst.Cores.TSCAssembly
import Submission.Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
import Submission.Work.FTS.EllSol.PkgK5.aSlot11T2
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.existsEllSolC_classC_noEst`

The class-`C` elliptic layer with **no estimate hypotheses**: the sibling
`Work.FTS.EllSol.existsEllSolC_classC_of` builds the frozen `Prop`
`Work.FTS.ClassC.ExistsEllSolC` out of the level-`8` existence node (A2) *and* the two uniform
elliptic estimates (`hEst4`, `hEst6`); here the estimates are **derived**, so that the existence
node alone suffices.

## The route

* the level-`0` estimate `TT.EllWeak0` is unconditional in the tree
  (`Work.FTS.EllipticEst.Dispatch.cores_level_zero`);
* the level-`2` estimate `TT.EllEstUnif 2` follows from it through the *piecewise* assembly
  `Work.FTS.EllipticEst.Cores.levelTwo_of_pieces` — **not** through the module-capping
  `Cores.levelTwo_fts`, whose axiom set carries `sorryAx` — with the two clean siblings
  `Cores.ShiftedTwoL2Clean` (the twice radially shifted `ℋ⁰`-slots) and
  `Cores.TopSlotsTwoClean_of` (the six level-`2` angular `Tk`-slots) applied to the `(1,1)`-slot
  bound `EllSol.PkgK5.aSlot11T2`;
* the induction step `Work.FTS.EllipticEst.Prop.step` (Elgindi's `prop:Hk`, `k ≥ 3`) is clean and
  lifts the level `k - 1` estimate to level `k`, giving `TT.EllEstUnif k` for every `k ≥ 2`
  (`Work.FTS.EllipticEst.TT.propHk_core_of`);
* instantiate at `k = 4`, `k = 6` and feed `existsEllSolC_classC_of`.

Every ingredient of the chain is `sorry`-free (axioms `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace Work.FTS.EllSol

set_option autoImplicit false

/-- **Elgindi's `prop:Hk` for every `k ≥ 2`**, unconditionally: the level-`0` estimate together
with the level-`2` assembly and the clean induction step. -/
theorem ellEstUnifAll : ∀ k : ℕ, 2 ≤ k →
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C :=
  Work.FTS.EllipticEst.TT.propHk_core_of
    Work.FTS.EllipticEst.Dispatch.cores_level_zero
    (Work.FTS.EllipticEst.Cores.levelTwo_of_pieces
      (Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
        Work.FTS.EllipticEst.Dispatch.cores_level_zero)
      (Work.FTS.EllipticEst.Cores.TopSlotsTwoClean_of
        (Work.FTS.EllSol.PkgK5.aSlot11T2 Work.FTS.EllipticEst.Dispatch.cores_level_zero)
        Work.FTS.EllipticEst.Dispatch.cores_level_zero)
      Work.FTS.EllipticEst.Dispatch.cores_level_zero)
    (fun k hk hprev => Work.FTS.EllipticEst.Prop.step k hk
      Work.FTS.EllipticEst.Dispatch.cores_level_zero hprev)

theorem existsEllSolC_classC_noEst
    (hb : ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.ClassC.ClassC α g → ∃ Ψ : Work.FTS.Galerkin.Fn,
        Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    Work.FTS.ClassC.ExistsEllSolC :=
  Work.FTS.EllSol.existsEllSolC_classC_of hb
    (ellEstUnifAll 4 (by norm_num)) (ellEstUnifAll 6 (by norm_num))

end Work.FTS.EllSol
