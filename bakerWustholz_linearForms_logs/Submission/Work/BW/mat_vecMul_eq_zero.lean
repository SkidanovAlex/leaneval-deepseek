import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If an integer square matrix `A` has nonzero determinant, then any integer vector `c` with
`∑ j, c j * A j b = 0` for every column index `b` must vanish. -/
theorem mat_vecMul_eq_zero {ρ : ℕ} (A : Matrix (Fin ρ) (Fin ρ) ℤ) (hA : A.det ≠ 0)
    (c : Fin ρ → ℤ) (hc : ∀ b, ∑ j, c j * A j b = 0) : c = 0 := by
  -- The hypothesis says that the row vector `c` annihilates every column of `A`;
  -- equivalently `Aᵀ *ᵥ c = 0`.
  have hB : Matrix.mulVec (Matrix.transpose A) c = 0 := by
    funext b
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hc b
  -- Multiply both sides on the left by the adjugate matrix: `adj(Aᵀ) * Aᵀ = det(Aᵀ) • 1`.
  have h1 : Matrix.mulVec (Matrix.adjugate (Matrix.transpose A) * Matrix.transpose A) c = 0 := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  have h2 : A.det • c = 0 := by
    have hh := h1
    rw [Matrix.adjugate_mul, Matrix.det_transpose, Matrix.smul_mulVec, Matrix.one_mulVec] at hh
    exact hh
  -- Hence `det A • c = 0`, and since `ℤ` is a domain with `det A ≠ 0`, `c = 0`.
  funext b
  have hb : A.det * c b = 0 := by
    have := congr_fun h2 b
    simpa using this
  exact (mul_eq_zero.mp hb).resolve_left hA

end Work.BW
