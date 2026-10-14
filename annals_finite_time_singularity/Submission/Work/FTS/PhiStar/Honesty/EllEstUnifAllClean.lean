import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllSol.PkgK5.aSlot11T2
import Submission.Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
import Submission.Work.FTS.EllipticEst.Cores.levelTwo_fts
import Submission.Work.FTS.EllipticEst.Final.Level0
import Submission.Work.FTS.GalFields.RHS.Fr_smooth_honest
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.Spaces.mixed_mul_le

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
