import Mathlib
import Submission.Commons.Data.Matrix.exists_unimodular_upperTriangular_columns

namespace Commons.Data.Matrix

/-- Every integer matrix with nonzero determinant is (row-)equivalent via a unimodular
integer matrix `U` to an upper triangular matrix: for each column `j`, the entries of
`U • column j` above the diagonal position `j` vanish, i.e. `(U.mulVec (fun r => A r j)) i = 0`
for all `j < i`.  (Equivalently `U * A` is upper triangular.) -/
theorem upperTriangular_of_det_ne_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hA : A.det ≠ 0) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ,
      IsUnit U.det ∧
      ∀ (i j : Fin d), j < i → (U.mulVec (fun r : Fin d => A r j)) i = 0 := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, ?unit, ?tri⟩
    · simp [Matrix.det_one]
    · intro i
      exact Fin.elim0 i
  · let z : Fin d → (Fin d → ℤ) := fun c r => A r c
    have hAeq : (Matrix.of (fun r : Fin d => fun c : Fin d => z c r)) = A := by
      ext r c
      simp [z, Matrix.of_apply]
    obtain ⟨U, hU, htri⟩ := exists_unimodular_upperTriangular_columns z hd (by
      rw [hAeq]
      exact hA)
    refine ⟨U, hU, ?_⟩
    intro i j hij
    exact htri j i hij

end Commons.Data.Matrix
