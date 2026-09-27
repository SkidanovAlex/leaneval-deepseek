import Mathlib
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

theorem mink_expand {n : ℕ} (x y z w : Fin n ⊕ Fin 1 → ℝ) (a b c d : ℝ) :
    Submission.Mostow.Hyper.mink (a • x + b • y) (c • z + d • w)
      = a * c * Submission.Mostow.Hyper.mink x z + a * d * Submission.Mostow.Hyper.mink x w
        + b * c * Submission.Mostow.Hyper.mink y z + b * d * Submission.Mostow.Hyper.mink y w := by
  simp only [Submission.Mostow.Hyper.mink, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end Work.Mostow
