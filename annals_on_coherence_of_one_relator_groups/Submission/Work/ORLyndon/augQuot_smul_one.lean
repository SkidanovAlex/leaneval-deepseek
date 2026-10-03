import Mathlib
import Submission.Work.ORLyndon.AugQuot

namespace Work.ORLyndon

universe u v

theorem augQuot_smul_one {K : Type v} [Field K] {G : Type u} [Group G]
    (n : MonoidAlgebra K G ⧸ Work.ORLyndon.augIdeal K G) :
    Work.ORLyndon.augQuot K G n • (1 : MonoidAlgebra K G ⧸ Work.ORLyndon.augIdeal K G)
      = n := by
  have h1 : Work.ORLyndon.augQuot K G n • (1 : MonoidAlgebra K G ⧸ augIdeal K G)
      = algebraMap K (MonoidAlgebra K G ⧸ augIdeal K G) (augQuot K G n) := by
    rw [Algebra.smul_def, mul_one]
  rw [h1]
  apply augQuotHom_injective K G
  rw [AlgHom.commutes]
  rfl

end Work.ORLyndon
