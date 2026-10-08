import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.cmtK0_mulEquiv_hypTorus
import Submission.Work.L2F.Conic.hypTorus_cyclic

open scoped MatrixGroups

namespace Work.L2F.Props

/-- The image in `PGL(2,F)` of the centralizer `cmtK0 F S` (where `S` is a non-scalar element of
`GL(2,F)` with `S * S = lam • 1`, `lam ≠ 0`) is cyclic: `cmtK0 F S ≃* hypTorus F lam`
(`Work.L2F.Props.cmtK0_mulEquiv_hypTorus`), `hypTorus F lam` is cyclic
(`Work.L2F.Conic.hypTorus_cyclic`), and a quotient of a cyclic group is cyclic. -/
theorem isCyclic_map_cmtK0 (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1) :
    IsCyclic ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) := by
  obtain ⟨e⟩ := Work.L2F.Props.cmtK0_mulEquiv_hypTorus F S lam hS hlam hns
  have hcyc : IsCyclic (Work.L2F.Props.cmtK0 F S) :=
    (MulEquiv.isCyclic e).mpr (Work.L2F.Conic.hypTorus_cyclic F h2 lam hlam)
  exact isCyclic_of_surjective
    ((Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* PGL(2, F)).subgroupMap
      (Work.L2F.Props.cmtK0 F S))
    (MonoidHom.subgroupMap_surjective _ _)

end Work.L2F.Props
