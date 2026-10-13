/-
# `Honesty.ellEstUnifAll_clean` — Elgindi's `prop:Hk` in a *LevelK-free* module

`Work.FTS.EllSol.ellEstUnifAll` (the unconditional form of Elgindi's `prop:Hk` for every
`k ≥ 2`) lives in `Submission/Work/FTS/EllSol/existsEllSolC_classC_noEst.lean`, a module that also
proves `existsEllSolC_classC_noEst` and therefore imports `EllSol.existsEllSolC_classC_of`, which
imports **`EllExist.LevelK`**.  Since `LevelK` is *downstream* of this directory's node
(`PhiStar.EllNode8tr_holds`), importing the original module from here would create an import cycle.

This file records the *same proof term* — the assembly of the level-`0` estimate
(`Dispatch.cores_level_zero`), the level-`2` estimate (`Cores.levelTwo_of_pieces` with its two
pieces) and the induction step (`Prop.step`) into `TT.propHk_core_of` — but imports only the
LevelK-free pieces of that module, under the name `ellEstUnifAll_clean`.

Nothing here is new mathematics: it is `Work.FTS.EllSol.ellEstUnifAll` re-homed so that it can be
used inside the cone of `EllNode8tr`.
-/
import Mathlib.Basic.Real.Basic
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

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **Elgindi's `prop:Hk` for every `k ≥ 2`**, unconditionally (LevelK-free copy of
`Work.FTS.EllSol.ellEstUnifAll`). -/
theorem ellEstUnifAll_clean : ∀ k : ℕ, 2 ≤ k →
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

end Work.FTS.PhiStar.Honesty
