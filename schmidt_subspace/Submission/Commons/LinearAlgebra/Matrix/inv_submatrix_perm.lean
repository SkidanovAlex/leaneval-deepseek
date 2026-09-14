import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Commons.LinearAlgebra.Matrix

theorem inv_submatrix_perm {n : ℕ} {K : Type*} [Field K] (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) K) :
    (A.submatrix σ σ)⁻¹ = A⁻¹.submatrix σ σ := by
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.det_submatrix_equiv_self,
    Matrix.adjugate_submatrix_equiv_self, Matrix.submatrix_smul]
  rfl

end Commons.LinearAlgebra.Matrix