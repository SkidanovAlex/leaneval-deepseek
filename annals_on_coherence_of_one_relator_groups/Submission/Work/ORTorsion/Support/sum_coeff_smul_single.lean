import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open Work.ORTorsion

theorem sum_coeff_smul_single {K : Type*} [Field K] {G : Type*} [Group G]
    (β : MonoidAlgebra K G) :
    β = ∑ g ∈ β.coeff.support,
      β.coeff g • (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single β]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [MonoidAlgebra.smul_single', mul_one]

end Work.ORTorsion.Support
