import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open scoped Matrix

theorem shearMat_entries (G : Matrix (Fin 3) (Fin 3) ℝ) (r : ℝ) :
    shearMat G r
      = !![G 0 0 + G 1 0 * r, G 0 1 + (G 1 1 - G 0 0) * r - G 1 0 * r ^ 2, G 0 2 + G 1 2 * r;
           G 1 0, G 1 1 - G 1 0 * r, G 1 2;
           G 2 0, G 2 1 - G 2 0 * r, G 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Work.EKLC8Core
