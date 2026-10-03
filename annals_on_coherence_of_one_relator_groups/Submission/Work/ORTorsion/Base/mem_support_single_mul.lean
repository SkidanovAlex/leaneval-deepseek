import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Base

open Work.ORTorsion

theorem mem_support_single_mul {K : Type*} [Field K] {G : Type*} [Group G] (a : G)
    (β : MonoidAlgebra K G) (h : G) :
    h ∈ (MonoidAlgebra.single a (1 : K) * β).coeff.support ↔ a⁻¹ * h ∈ β.coeff.support := by
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, MonoidAlgebra.coeff_single_mul_apply,
    one_mul]

end Work.ORTorsion.Base
