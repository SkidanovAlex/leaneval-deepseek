import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# The cofactor vector lies in the kernel

For a linear map `T : ℝ^{m+1} → ℝ^m` the cofactor vector `cofactorVec T` — the vector whose `j`-th
component is the signed maximal minor of the matrix of `T` with the `j`-th row deleted — satisfies
`T (cofactorVec T) = 0`.  In other words the cofactor vector is orthogonal to every column of the
matrix of `T`.

The proof is the classical one: the `k`-th component of `T (cofactorVec T)` is
`∑ j, (cofactorVec T) j * A j k` (where `A = cofactorMatrix T`), and this sum is the determinant
expansion along the first column of a square matrix obtained from `A` by prepending a duplicate of
the `k`-th column of `A`; a determinant with a repeated column vanishes.
-/

namespace Work.Drive

/-- The `(m+1) × (m+1)` matrix obtained from `A : Matrix (Fin (m+1)) (Fin m) ℝ` by prepending a
duplicate of its `k`-th column: the first column is the `k`-th column of `A`, the remaining columns
are the columns of `A` in order. -/
def augMat {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin m) ℝ) (k : Fin m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun j col => Fin.cases (A j k) (fun i => A j i) col

/-- **Cofactor identity.**  For `A : Matrix (Fin (m+1)) (Fin m) ℝ`, the cofactor vector
`c j = (-1)^j * det (A with row j deleted)` is orthogonal to every column of `A`. -/
theorem sum_cofactor_mul_eq_zero {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin m) ℝ) (k : Fin m) :
    ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (A.submatrix (Fin.succAbove j) id).det) * A j k
      = 0 := by
  have hB0 : ∀ j, augMat A k j 0 = A j k := by intro j; simp [augMat]
  have hBsucc : ∀ (j : Fin (m + 1)) (i : Fin m), augMat A k j (Fin.succ i) = A j i := by
    intro j i; simp [augMat]
  -- the augmented matrix has two equal columns, namely the `0`-th and the `(k+1)`-st
  have hdet : (augMat A k).det = 0 := by
    refine Matrix.det_zero_of_column_eq (i := (0 : Fin (m + 1))) (j := Fin.succ k) ?_ ?_
    · exact (Fin.succ_ne_zero k).symm
    · intro r; rw [hB0 r, hBsucc r k]
  have hsub : ∀ i : Fin (m + 1),
      (augMat A k).submatrix i.succAbove Fin.succ = A.submatrix i.succAbove id := by
    intro i; ext a b; simp [Matrix.submatrix_apply, hBsucc]
  -- Laplace expansion along the first column
  have hexp := Matrix.det_succ_column_zero (augMat A k)
  rw [hdet] at hexp
  simp only [hB0] at hexp
  simp only [hsub] at hexp
  have key : (∑ i : Fin (m + 1),
        ((-1 : ℝ) ^ (i : ℕ) * (A.submatrix (Fin.succAbove i) id).det) * A i k)
      = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * A i k * (A.submatrix (Fin.succAbove i) id).det := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [key]
  exact hexp.symm

theorem cofactorVec_mem_ker {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m) :
    T (Work.Drive.cofactorVec T) = 0 := by
  -- decompose `cofactorVec T` in the standard basis of `ℝ^{m+1}`
  have hvec : Work.Drive.cofactorVec T =
      ∑ j : Fin (m + 1), (Work.Drive.cofactorVec T) j • EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin (m + 1))).sum_repr (Work.Drive.cofactorVec T)]
    simp [PiLp.basisFun_repr, PiLp.basisFun_apply]
  ext k
  rw [hvec, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_zero, WithLp.ofLp_smul, Pi.zero_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Work.Drive.cofactorVec, WithLp.ofLp_toLp]
  exact sum_cofactor_mul_eq_zero (Work.Drive.cofactorMatrix T) k

end Work.Drive
