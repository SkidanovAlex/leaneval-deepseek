import Mathlib

namespace Work.Drive

/-- Prepending a column `v` to an `(m+1) × m` matrix `A` yields a square matrix whose determinant
vanishes exactly when `v` lies in the span of the columns of `A`, provided those columns are
linearly independent. -/
theorem det_prependCol_eq_zero_iff_mem_span {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ)
    (hA : LinearIndependent ℝ A.col) (v : Fin (m+1) → ℝ) :
    (Matrix.of fun j => Fin.cons (v j) (A j)).det = 0 ↔ v ∈ Submodule.span ℝ (Set.range A.col) := by
  set B : Matrix (Fin (m+1)) (Fin (m+1)) ℝ := Matrix.of fun j => Fin.cons (v j) (A j)
  -- The columns of `B` are `v` followed by the columns of `A`.
  have hcol : B.col = Fin.cons v A.col := by
    funext i j
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨k+1, _⟩ => rfl
  -- A square matrix over a field has zero determinant iff its columns are linearly dependent.
  have hdet : B.det = 0 ↔ ¬ LinearIndependent ℝ B.col := by
    rw [Matrix.linearIndependent_col_iff, Matrix.nonsingular_iff_det_ne_zero]
    simp [ne_eq]
  rw [hdet, hcol, linearIndependent_finCons]
  simp [hA]

end Work.Drive
