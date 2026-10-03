import Mathlib
import Submission.Work.OROneRel.case2_substitution

universe u

namespace Work.ORLocInd.CohenLyndon

theorem sigma_t_subst_cyclic {α : Type u} {r : FreeGroup α} {t x : α} (hxt : x ≠ t) :
    Work.OROneRel.sigma t (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
        (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r) = 1 := by
  rw [Work.OROneRel.c2s_sigma_t_subst hxt (Multiplicative.toAdd (Work.OROneRel.sigma x r))
    (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r]
  exact Work.OROneRel.c2s_ofAdd_zpow_mul_zpow _ _

end Work.ORLocInd.CohenLyndon
