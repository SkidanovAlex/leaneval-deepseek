import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_L1
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

open Work.FTS.CoercivityFix.Transfer (CommSm CommSm_L1 CommSm_succ AddOKSm)
open Work.FTS.CoercivityFix.Assembly (IP2 IP3 IP4)
open Work.Coercivity (H1IP HkIPStep)

theorem IP6AddFin {α : ℝ} {u v w : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hu : ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hv : ContDiffOn ℝ 6 (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (hw : ContDiffOn ℝ 6 (Function.uncurry w) Work.FTS.EllipticEst.Q0)
    (hmu : Work.Spaces.HkMem α 6 u) (hmv : Work.Spaces.HkMem α 6 v)
    (hmw : Work.Spaces.HkMem α 6 w) :
    Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (fun z θ => u z θ + v z θ) w
      = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α u w
        + Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α v w := by
  -- The finite-order algebraic package `CommSm` climbs the paper's recursion
  -- `IP^{k+1} = IP^k + c₁ IP^k(D_θ·,D_θ·) + c₂ IP^k(D_z·,D_z·)` five times, from the
  -- level-`1` base `H1IP` up to the level-`6` pairing `IP6`.  Its `add` clause takes exactly
  -- the hypotheses at hand: `C⁶` on the open quadrant (the finite order that the level-`6`
  -- pairing consumes) and `ℋ⁶`-membership.
  have h1 : CommSm α 1 (H1IP α) := CommSm_L1 α hα
  have h2 : CommSm α 2 (IP2 1 1 α) := CommSm_succ α hα 1 h1
  have h3 : CommSm α 3 (IP3 1 1 1 1 α) := CommSm_succ α hα 2 h2
  have h4 : CommSm α 4 (IP4 1 1 1 1 1 1 α) := CommSm_succ α hα 3 h3
  have h5 : CommSm α 5 (HkIPStep 1 1 (IP4 1 1 1 1 1 1 α)) := CommSm_succ α hα 4 h4
  have h6 : CommSm α 6 (HkIPStep 1 1 (HkIPStep 1 1 (IP4 1 1 1 1 1 1 α))) :=
    CommSm_succ α hα 5 h5
  exact h6.add u v w ⟨hu, hv, hw, hmu, hmv, hmw⟩

end Work.FTS.StrongPersist
