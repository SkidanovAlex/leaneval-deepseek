import Mathlib
import Submission.Work.OROneRel.sigma_mk
import Submission.Work.OROneRel.rewrite_isCyclicallyReduced_of_expsum_zero

namespace Work.OROneRel

universe u

theorem eps_eq_toAdd_sigma {α : Type u} (t : α) (r : FreeGroup α) :
    Work.OROneRel.eps t r = (Work.OROneRel.sigma t r).toAdd := by
  classical
  have h1 : Work.OROneRel.sigma t r =
      Multiplicative.ofAdd (Work.OROneRel.sigmaList t r.toWord) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := r)]
    exact Work.OROneRel.sigma_mk t r.toWord
  rw [h1]
  show Work.OROneRel.eps t r =
    (Multiplicative.ofAdd (Work.OROneRel.sigmaList t r.toWord)).toAdd
  rw [show (Multiplicative.ofAdd (Work.OROneRel.sigmaList t r.toWord)).toAdd
        = Work.OROneRel.sigmaList t r.toWord from rfl]
  exact (show Work.OROneRel.eps t r = Work.OROneRel.sigmaList t r.toWord from rfl)

end Work.OROneRel
