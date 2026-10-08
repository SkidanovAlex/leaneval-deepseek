import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.centralizer_aux

namespace Work.L2F.Torus

/-- The centralizer of `x` in `SL(2,F)` is exactly the set of `a • 1 + b • conjMat F x` with
`a² - disc F x * b² = 1`. -/
theorem mem_centralizer_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (x u : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0) : u ∈ cent F x ↔ ∃ a b : F, a ^ 2 - disc F x * b ^ 2 = 1 ∧ (u : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • conjMat F x := by
  have hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4 := by
    rw [disc_apply] at hD
    exact sub_ne_zero.mp hD
  rw [cent_apply]
  exact Work.L2F.Mat2.mem_centralizer_iff_smul_one_add F h2 x hx u

end Work.L2F.Torus
