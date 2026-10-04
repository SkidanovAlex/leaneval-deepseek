import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary facts for `Work.Diff.Alg.Pinch.EFun_X_strict_at_degenerate`

Elementary orthogonal-matrix and frame-transport facts used both by the reduction of the
`D`-part to the diagonal-Ricci case (`Work.Diff.Alg.Pinch.Dtensor_pos_reduce`) and by the
final assembly.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

open scoped Matrix

variable {n : ℕ}

lemma one_mem_orthogonalGroup (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
  (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mpr (by simp)

/-- The rows of a matrix in `O(n)`: `∑ i, A k i * A l i = δ_{k l}`. -/
lemma row_sum_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A * Aᵀ = 1) (k l : Fin n) : ∑ i, A k i * A l i = if k = l then 1 else 0 := by
  have h1 : (A * Aᵀ) k l = ∑ i, A k i * A l i := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← h1, hA, Matrix.one_apply]

/-- The columns of a matrix in `O(n)`: `∑ i, A i k * A i l = δ_{k l}`. -/
lemma col_sum_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ * A = 1) (k l : Fin n) : ∑ i, A i k * A i l = if k = l then 1 else 0 := by
  have h1 : (Aᵀ * A) k l = ∑ i, A i k * A i l := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [← h1, hA, Matrix.one_apply]

/-- `rot A (Iso n) = Iso n` for orthogonal `A`. -/
lemma rot_Iso_of_orthogonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) : rot A (Iso n) = Iso n := by
  have hAA : A * Aᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA
  have hrow := row_sum_eq n A hAA
  funext i j k l
  rw [rot_Iso]
  simp only [hrow i k, hrow j l, hrow i l, hrow j k, Iso]

end Work.Diff.Alg.Pinch
