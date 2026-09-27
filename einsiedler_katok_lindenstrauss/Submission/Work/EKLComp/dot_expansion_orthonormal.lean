import Mathlib

namespace Work.EKLComp

theorem dot_expansion_orthonormal (e1 e2 u y : Fin 3 → ℝ)
    (h1 : ∑ i, e1 i * e1 i = 1) (h2 : ∑ i, e2 i * e2 i = 1) (h3 : ∑ i, u i * u i = 1)
    (h12 : ∑ i, e1 i * e2 i = 0) (h1u : ∑ i, e1 i * u i = 0) (h2u : ∑ i, e2 i * u i = 0) :
    (∑ i, y i * y i) = (∑ i, e1 i * y i)^2 + (∑ i, e2 i * y i)^2 + (∑ i, u i * y i)^2 := by
  -- Assemble the three orthonormal vectors as the rows of a 3×3 real matrix.
  let R : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![e1, e2, u]
  -- The rows are orthonormal, i.e. R * Rᵀ = 1.
  have hR : R * R.transpose = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Matrix.mul_apply, Matrix.transpose_apply, h1, h2, h3, h12, h1u, h2u, mul_comm]
  -- Since R is a square matrix over a commutative ring, R * Rᵀ = 1 implies Rᵀ * R = 1.
  have hRt : R.transpose * R = 1 := mul_eq_one_comm.mp hR
  -- The components of R * y are the three inner products with e1, e2, u.
  have hRv0 : (R.mulVec y) 0 = ∑ i, e1 i * y i := by
    simp [R, Matrix.mulVec, dotProduct]
  have hRv1 : (R.mulVec y) 1 = ∑ i, e2 i * y i := by
    simp [R, Matrix.mulVec, dotProduct]
  have hRv2 : (R.mulVec y) 2 = ∑ i, u i * y i := by
    simp [R, Matrix.mulVec, dotProduct]
  -- Parseval: the squared norm of R * y equals the squared norm of y.
  have key : (R.mulVec y) ⬝ᵥ (R.mulVec y) = ∑ i, y i * y i := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose R (R.mulVec y),
      Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]
    rfl
  calc (∑ i, y i * y i) = (R.mulVec y) ⬝ᵥ (R.mulVec y) := key.symm
    _ = (R.mulVec y) 0 * (R.mulVec y) 0 + (R.mulVec y) 1 * (R.mulVec y) 1
          + (R.mulVec y) 2 * (R.mulVec y) 2 := by
        rw [dotProduct, Fin.sum_univ_three]
    _ = (∑ i, e1 i * y i)^2 + (∑ i, e2 i * y i)^2 + (∑ i, u i * y i)^2 := by
        rw [hRv0, hRv1, hRv2]; ring

end Work.EKLComp
