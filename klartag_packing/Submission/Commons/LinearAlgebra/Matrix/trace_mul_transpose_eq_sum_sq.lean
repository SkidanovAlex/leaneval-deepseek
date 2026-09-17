import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Commons.LinearAlgebra.Matrix

/-- The trace of `A * Aᵀ` equals the sum of squares of the entries of `A`
(the Frobenius norm squared of `A`). -/
theorem trace_mul_transpose_eq_sum_sq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    (A * A.transpose).trace = ∑ i, ∑ j, A i j * A i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

end Commons.LinearAlgebra.Matrix