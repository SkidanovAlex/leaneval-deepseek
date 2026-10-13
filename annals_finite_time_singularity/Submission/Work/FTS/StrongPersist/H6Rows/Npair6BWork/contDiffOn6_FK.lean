import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- The datum data of the level-six coefficient rows records only *finite-order* smoothness
(`SmoothOpen f` is `C^∞` on the open quadrant) together with `HkMem α 7 f`, so the radial
angular moment `z ↦ FK f z` is `C^6` on the open quadrant: this is exactly
`H6Rows.co6_FK_radial`.  (The `C^∞`-strength statement `SmoothOpen (FK f)` is false for honest
data, see `Npair6BWork/NOTES_coefData_FK_FALSE.md`; order six is the right interface.) -/
theorem contDiffOn6_FK : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
    Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
    ContDiffOn ℝ 6
      (Function.uncurry (fun z _ => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  exact Work.FTS.StrongPersist.H6Rows.co6_FK_radial hα0 hα1 hD.sm hD.h7

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
