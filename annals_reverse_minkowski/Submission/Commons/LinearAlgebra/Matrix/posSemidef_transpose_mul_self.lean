import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Commons.LinearAlgebra.Matrix

/-- For any real square matrix `A`, the product `Aᵀ * A` is positive semidefinite. -/
theorem posSemidef_transpose_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.transpose * A).PosSemidef := by
  -- Over `ℝ` the conjugate transpose coincides with the transpose, and Mathlib
  -- provides `Matrix.posSemidef_conjTranspose_mul_self`.
  simpa using Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) A

end Commons.LinearAlgebra.Matrix