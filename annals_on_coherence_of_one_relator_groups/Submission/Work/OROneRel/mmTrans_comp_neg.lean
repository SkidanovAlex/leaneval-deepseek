import Mathlib
import Submission.Work.OROneRel.mmTransvectionDefs

namespace Work.OROneRel

theorem mmTrans_comp_neg {α : Type*} (t : α) (m : α → ℤ) (hmt : m t = 0) :
    (Work.OROneRel.mmTrans t (fun x => -(m x))).comp (Work.OROneRel.mmTrans t m) =
        MonoidHom.id (FreeGroup α) ∧
      (Work.OROneRel.mmTrans t m).comp (Work.OROneRel.mmTrans t (fun x => -(m x))) =
        MonoidHom.id (FreeGroup α) := by
  constructor <;>
    · ext x
      simp [mmTrans_of, hmt, map_mul, map_zpow]

end Work.OROneRel
