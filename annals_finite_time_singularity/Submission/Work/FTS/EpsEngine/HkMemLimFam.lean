import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllSol.PkgK5.aSlot11T2
import Submission.Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
import Submission.Work.FTS.EllipticEst.Cores.levelTwo_fts
import Submission.Work.FTS.EllipticEst.Final.Level0
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam
import Submission.Work.FTS.GalFields.RHS.Fr_smooth_honest
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllSol.existsEllSolC_classC_noEst =====
section

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


end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkMemLimFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps.EpsLocalPStar (iter)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EpsEngine
end
end
