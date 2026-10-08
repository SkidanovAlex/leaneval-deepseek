import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Mat2

/-- Cayley–Hamilton for `2 × 2` matrices: `M * M = tr M • M - det M • 1`.
Proof: `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.det_fin_two,
Matrix.trace_fin_two] <;> ring`. -/
theorem sq_eq_trace_smul_sub_det (F : Type*) [Field F] (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

end Work.L2F.Mat2
