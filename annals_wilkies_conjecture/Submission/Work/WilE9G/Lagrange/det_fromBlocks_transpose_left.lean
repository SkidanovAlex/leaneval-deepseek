import Mathlib

namespace Work.WilE9G.Lagrange

/-- For any `A` and `W`, the determinant of the block matrix `[[A, W], [-Wᵀ, 0]]` is unchanged when
the top-left block `A` is replaced by its transpose. -/
theorem det_fromBlocks_transpose_left {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) :
    (Matrix.fromBlocks A W (-W.transpose) 0).det
      = (Matrix.fromBlocks A.transpose W (-W.transpose) 0).det := by
  -- Let `E = diag(I_r, -I_j)`.  The key point is that `E * Mᵀ * E = M'`, so the two matrices
  -- are determinants of congruent (in fact similar) matrices; since `det E * det E = 1`, the
  -- determinants agree.
  set E : Matrix (Fin r ⊕ Fin j) (Fin r ⊕ Fin j) ℝ := Matrix.fromBlocks 1 0 0 (-1) with hE
  have hEE : E * E = 1 := by
    rw [hE, Matrix.fromBlocks_multiply]
    simp
  have hE2 : E.det * E.det = 1 := by
    rw [← Matrix.det_mul, hEE, Matrix.det_one]
  -- the transpose of `[[A, W], [-Wᵀ, 0]]`
  have hT : (Matrix.fromBlocks A W (-W.transpose) 0).transpose
      = Matrix.fromBlocks A.transpose (-W) W.transpose 0 := by
    rw [Matrix.fromBlocks_transpose]
    simp
  -- conjugating that transpose by `E` returns the target matrix
  have hconj : E * Matrix.fromBlocks A.transpose (-W) W.transpose 0 * E
      = Matrix.fromBlocks A.transpose W (-W.transpose) 0 := by
    rw [hE, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    exact ⟨by simp, by simp, by simp, by simp⟩
  have hM' : Matrix.fromBlocks A.transpose W (-W.transpose) 0
      = E * (Matrix.fromBlocks A W (-W.transpose) 0).transpose * E := by
    rw [hT, hconj]
  have key : (E.det * (Matrix.fromBlocks A W (-W.transpose) 0).det) * E.det
      = (Matrix.fromBlocks A W (-W.transpose) 0).det := by
    calc (E.det * (Matrix.fromBlocks A W (-W.transpose) 0).det) * E.det
        = (Matrix.fromBlocks A W (-W.transpose) 0).det * (E.det * E.det) := by ring
      _ = (Matrix.fromBlocks A W (-W.transpose) 0).det * 1 := by rw [hE2]
      _ = (Matrix.fromBlocks A W (-W.transpose) 0).det := mul_one _
  rw [hM', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact key.symm

end Work.WilE9G.Lagrange
