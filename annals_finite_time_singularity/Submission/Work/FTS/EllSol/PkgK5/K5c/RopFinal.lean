/-
# `K5c/RopFinal` — the `U`-slot at levels `2 ≤ k ≤ 5` from the wall

`Work.FTS.EllSol.PkgK5.uopTransferK5c` is the `U`-slot of the pinned `K5` elliptic package.
Its only input beyond the elliptic data of the `EllClassOk` chain is the *wall*
`Work.FTS.EllSol.PkgK5.WallK5 k` (`α D_z∂_θV ∈ ℋ^k` with its `ℋ^k`-estimate), which the sibling
module `PkgK5.uopTransferK5c_of_wall` consumes.

This module supplies the wall from the *proved* trace brick: `K5c.wallBrick` (whose proof is the
assembly `K5c.famBrick` of `TraceEngine.traceBrick` and `TraceEngine.slotBounds` into the family
interpolation, followed by the transpose of `PkgK5.wall_of_interp`), and then instantiates
`uopTransferK5c_of_wall`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllSol.PkgK5.WallDefs
import Submission.Work.FTS.EllSol.PkgK5.uopTransferK5c_of_wall
import Submission.Work.FTS.EllSol.PkgK5.K5c.WallBrick

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.K5c

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The wall at levels `2 ≤ k ≤ 5`, from the trace brick. -/
theorem wallK5c (k : ℕ) (hk : 2 ≤ k) : Work.FTS.EllSol.PkgK5.WallK5 k := wallBrick k hk

/-- **The `U`-slot at levels `2 ≤ k ≤ 5`**, i.e. the statement of
`Work.FTS.EllSol.PkgK5.uopTransferK5c`, proved from the wall (`K5c.wallBrick`). -/
theorem uopTransferK5c_c (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ) ∧
      Work.Spaces.HkNorm α k (fun z θ =>
          Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ / Work.Construction.s2 θ)
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) :=
  Work.FTS.EllSol.PkgK5.uopTransferK5c_of_wall k hk hk5 (wallK5c k hk)

end Work.FTS.EllSol.PkgK5.K5c
