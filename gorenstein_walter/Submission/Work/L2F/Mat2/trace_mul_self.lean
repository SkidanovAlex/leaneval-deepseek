import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Mat2

/-- Newton's identity for `2 × 2` matrices: `tr(M²) = (tr M)² - 2 det M`.
Proof: expand with `Matrix.trace_fin_two`, `Matrix.det_fin_two`, `Matrix.mul_apply`; `ring`. -/
theorem trace_mul_self (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    (M * M).trace = M.trace ^ 2 - 2 * M.det := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end Work.L2F.Mat2
