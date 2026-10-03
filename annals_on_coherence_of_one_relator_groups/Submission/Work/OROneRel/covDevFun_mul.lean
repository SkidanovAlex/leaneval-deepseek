import Mathlib
import Submission.Work.OROneRel.covCollapseDefs

namespace Work.OROneRel

theorem covDevFun_mul {α : Type*} (W : ℤ → FreeGroup α) (c : α → ℤ) (k : ℤ) (u v : FreeGroup α) :
    Work.OROneRel.covDevFun W c k (u * v) =
      Work.OROneRel.covDevFun W c k u *
        Work.OROneRel.covDevFun W c (k + (Work.OROneRel.cohom c u).toAdd) v := by
  have hab : u * v = FreeGroup.mk (wordOf u ++ wordOf v) := by
    rw [mk_append, mk_wordOf, mk_wordOf]
  rw [hab, covDevFun_mk, covDevAux_append, covDevAux_wordOf, covDevAux_wordOf, lsig_wordOf]

end Work.OROneRel
