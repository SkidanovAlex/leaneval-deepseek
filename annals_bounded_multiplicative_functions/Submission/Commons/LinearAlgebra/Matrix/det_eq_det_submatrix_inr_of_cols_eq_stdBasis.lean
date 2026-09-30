import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.LinearAlgebra.Matrix

/-- If the columns indexed by `Sum.inl` of a square matrix indexed by `Fin m ⊕ Fin n` are
exactly the standard basis vectors `e_{inl i}`, then the determinant equals the determinant
of the lower-right `Fin n × Fin n` block. -/
theorem det_eq_det_submatrix_inr_of_cols_eq_stdBasis {m n : ℕ}
    (A : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
    (h : ∀ (i : Fin m) (c : Fin m ⊕ Fin n),
      A c (Sum.inl i) = if c = Sum.inl i then (1 : ℝ) else 0) :
    A.det = (A.submatrix Sum.inr Sum.inr).det := by
  have hA : A = Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℝ)
      (A.submatrix Sum.inl Sum.inr) 0 (A.submatrix Sum.inr Sum.inr) := by
    ext r c
    rcases r with i | i <;> rcases c with j | j
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, h j (Sum.inl i)]
      simp only [Sum.inl.injEq]
    · simp [Matrix.submatrix_apply]
    · rw [Matrix.fromBlocks_apply₂₁, h j (Sum.inr i)]
      simp
    · simp [Matrix.submatrix_apply]
  conv_lhs => rw [hA]
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end Commons.LinearAlgebra.Matrix