import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.foxD_zeta_of_ne_clean

namespace Work.ORLyndon

theorem foxD_eq_sum_zeta_magRewRel {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (u : FreeGroup α) (hσ : Work.OROneRel.sigma t u = 1) :
    Work.ORLyndon.foxD (K := K) x u =
      (Work.ORLyndon.foxFD (K := K) (Work.OROneRel.magRewRel t u)).sum (fun q c =>
        if (q.1 : α) = x then
          MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t) c *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0) := by
  conv_lhs => rw [Work.ORLyndon.eq_zeta_magRewRel t u hσ]
  exact Work.ORLyndon.FoxZeta.foxD_zeta_of_ne (K := K) t x hxt (Work.OROneRel.magRewRel t u)

end Work.ORLyndon
