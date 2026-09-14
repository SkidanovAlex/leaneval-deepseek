import Mathlib.LinearAlgebra.Matrix.Adjugate

open Matrix

namespace Commons.LinearAlgebra.Matrix

theorem sum_mul_adjugate_eq {K : Type*} [CommRing K] {N : ℕ} (L : Matrix (Fin N) (Fin N) K)
    (x h : Fin N → K) :
    ∑ i, (∑ j, L i j * x j) * (∑ j, L.adjugate j i * h j) = L.det * ∑ j, x j * h j := by
  have hLHS : (∑ i, (∑ j, L i j * x j) * (∑ j, L.adjugate j i * h j))
      = (L *ᵥ x) ⬝ᵥ (L.adjugateᵀ *ᵥ h) := by
    simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
  rw [hLHS, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.transpose_mul,
    Matrix.adjugate_mul, Matrix.transpose_smul, Matrix.transpose_one, Matrix.vecMul_smul,
    Matrix.vecMul_one, smul_dotProduct, smul_eq_mul]
  congr 1

end Commons.LinearAlgebra.Matrix