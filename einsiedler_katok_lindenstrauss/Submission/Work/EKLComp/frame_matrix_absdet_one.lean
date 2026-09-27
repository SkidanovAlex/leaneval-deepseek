import Mathlib

namespace Work.EKLComp

open Matrix

/-- The rows `e1, e2, u` form an orthonormal basis of `ℝ³` (they are pairwise
orthogonal and each has unit norm), hence the matrix whose rows they are has
determinant of absolute value one. -/
theorem frame_matrix_absdet_one (e1 e2 u : Fin 3 → ℝ)
    (h1 : ∑ i, e1 i * e1 i = 1) (h2 : ∑ i, e2 i * e2 i = 1) (h3 : ∑ i, u i * u i = 1)
    (h12 : ∑ i, e1 i * e2 i = 0) (h1u : ∑ i, e1 i * u i = 0) (h2u : ∑ i, e2 i * u i = 0) :
    |(Matrix.of ![e1, e2, u]).det| = 1 := by
  simp only [Fin.sum_univ_three] at h1 h2 h3 h12 h1u h2u
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![e1, e2, u] with hM
  -- The Gram matrix of the rows is the identity: `M * Mᵀ = 1`.
  have hmul : M * Mᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, mul_comm] <;>
      first
       | exact h1 | exact h2 | exact h3
       | exact h12 | exact h1u | exact h2u
  -- Hence `det M * det M = det (M * Mᵀ) = det 1 = 1`, so `(det M)² = 1`.
  have hdet : M.det * M.det = 1 := by
    have := congrArg Matrix.det hmul
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hh : M.det ^ 2 = 1 := by nlinarith [hdet]
  have h2 : |M.det| ^ 2 = 1 := by rw [sq_abs, hh]
  nlinarith [abs_nonneg M.det, h2]

end Work.EKLComp
