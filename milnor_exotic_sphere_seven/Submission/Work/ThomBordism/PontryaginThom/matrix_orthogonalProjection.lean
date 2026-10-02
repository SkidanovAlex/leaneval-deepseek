import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism.PontryaginThom

/-- For an injective real matrix `A : Matrix (Fin m) (Fin n) ℝ`, the matrix
`P = A * (Aᵀ * A)⁻¹ * Aᵀ` is the orthogonal projection onto the image of `A`:
it fixes `A` (i.e. `P * A = A`), it is idempotent, it is symmetric, and it
annihilates the orthogonal complement of the range of `A`
(`Aᵀ * (1 - P) = 0`). -/
theorem matrix_orthogonalProjection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective (Matrix.toLin' A)) :
    (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A) * A = A ∧
    (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A)
        * (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A)
      = A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A ∧
    Matrix.transpose (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A)
      = A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A ∧
    Matrix.transpose A * (1 - A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A) = 0 := by
  -- Injectivity of `A` as a linear map is injectivity of `mulVec`.
  have hAmul : Function.Injective A.mulVec := by
    intro x y hxy
    apply hA
    simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply, hxy]
  -- Hence the Gram matrix `Aᵀ * A` is positive definite, so invertible.
  have hPos : ((Matrix.transpose A * A) : Matrix (Fin n) (Fin n) ℝ).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self A hAmul
  have hdet : IsUnit ((Matrix.transpose A * A).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPos.isUnit
  have h1 : (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A) * A = A := by
    rw [Matrix.mul_assoc (A * (Matrix.transpose A * A)⁻¹) (Matrix.transpose A) A,
      Matrix.mul_assoc A (Matrix.transpose A * A)⁻¹ (Matrix.transpose A * A),
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A)
          (A * (Matrix.transpose A * A)⁻¹) (Matrix.transpose A),
        ← Matrix.mul_assoc (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A) A
          (Matrix.transpose A * A)⁻¹, h1]
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc]
  · rw [Matrix.mul_sub, Matrix.mul_one]
    have hAte : Matrix.transpose A * (A * (Matrix.transpose A * A)⁻¹ * Matrix.transpose A)
        = Matrix.transpose A := by
      rw [← Matrix.mul_assoc (Matrix.transpose A) (A * (Matrix.transpose A * A)⁻¹)
            (Matrix.transpose A),
        ← Matrix.mul_assoc (Matrix.transpose A) A (Matrix.transpose A * A)⁻¹,
        Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    rw [hAte, sub_self]

end Work.ThomBordism.PontryaginThom
