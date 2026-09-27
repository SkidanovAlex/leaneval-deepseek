import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.linearIndependent_cols_cofactorMatrix
import Submission.Work.Drive.det_prependCol_eq_zero_iff_mem_span

/-!
# The kernel of a surjective `T : ℝ^{m+1} → ℝ^m` is spanned by the cofactor vector

For a linear map `T : ℝ^{m+1} → ℝ^m` with matrix `A = cofactorMatrix T`, the cofactor vector
`cofactorVec T` (`j`-th component `(-1)^j · det(A with row j deleted)`) spans the kernel of `T`
whenever `T` is surjective.

The proof is elementary linear algebra, done through determinants:

* `det_prependCol_aux` (Laplace expansion along the first column): prepending an arbitrary vector
  `v` as a first column to `A` gives a square matrix whose determinant is the cofactor functional
  `v ↦ ∑ j, (-1)^j v j det (A with row j deleted)`; combined with the inner product on `ℝ^{m+1}`
  this reads `⟪toLp v, cofactorVec T⟫ = det [v | A]`.
* `det_prependCol_col_aux`: prepending a *column* of `A` duplicates a column, so that determinant
  vanishes; hence `cofactorVec T` is orthogonal to every column of `A`.
* `det_prependCol_eq_zero_iff_mem_span` (colleague's lemma): the determinant of `[v | A]` vanishes
  exactly on the span of the columns of `A`, provided those columns are linearly independent;
* `linearIndependent_cols_cofactorMatrix` (colleague's lemma): surjectivity of `T` makes the
  columns of `A` linearly independent.
* `span_colVec_eq_comap_aux` transports the span of the columns from `Fin (m+1) → ℝ` to the
  Euclidean space `Amb m`.

Consequently the column space is the orthogonal complement of `ℝ · cofactorVec T`, and
`ker T = (column space)ᗮ = (ℝ · cofactorVec T)ᗮᗮ = ℝ · cofactorVec T`.
-/

namespace Work.Drive

open Matrix

noncomputable section

/-- The `i`-th column of `A : Matrix (Fin (m+1)) (Fin m) ℝ`, viewed as a vector of the ambient
space `Amb m = ℝ^{m+1}`. -/
def cofactorColVec {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ) : Fin m → Amb m :=
  fun i => WithLp.toLp 2 (A.col i)

/-- **Laplace expansion along the first column.**  Prepending `v` to `A` as a first column gives the
square matrix `[v | A]`, whose determinant is `∑ j, (-1)^j v j det (A with row j deleted)`. -/
theorem det_prependCol_aux {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ) (v : Fin (m+1) → ℝ) :
    (Matrix.of fun j => Fin.cons (v j) (A j)).det
      = ∑ j : Fin (m+1), (-1 : ℝ) ^ (j : ℕ) * v j * ((A.submatrix (Fin.succAbove j) id).det) := by
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : (Matrix.of fun i => Fin.cons (v i) (A i)).submatrix j.succAbove Fin.succ
      = A.submatrix j.succAbove id := by
    ext a b
    simp [Matrix.submatrix_apply, Fin.cons_succ]
  rw [hsub]
  simp [Matrix.of_apply, Fin.cons_zero]

/-- The determinant of `[v | A]` is the cofactor functional applied to `v`, i.e. the inner product
with the cofactor vector. -/
theorem inner_toLp_eq_det_aux {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ) (v : Fin (m+1) → ℝ) :
    inner ℝ (WithLp.toLp 2 v)
        (WithLp.toLp 2 (fun j => (-1 : ℝ) ^ (j : ℕ) * ((A.submatrix (Fin.succAbove j) id).det)))
      = (Matrix.of fun j => Fin.cons (v j) (A j)).det := by
  rw [det_prependCol_aux, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply]
  simp
  ring

/-- The same identity in terms of `cofactorVec`. -/
theorem inner_cofactorVec_toLp_aux {m : ℕ} (T : Amb m →L[ℝ] Tgt m) (v : Fin (m+1) → ℝ) :
    inner ℝ (WithLp.toLp 2 v) (cofactorVec T)
      = (Matrix.of fun j => Fin.cons (v j) (cofactorMatrix T j)).det :=
  inner_toLp_eq_det_aux (cofactorMatrix T) v

/-- Prepending a duplicate of the `i`-th column of `A` to `A` kills the determinant: the resulting
square matrix has two equal columns. -/
theorem det_prependCol_col_aux {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ) (i : Fin m) :
    (Matrix.of fun j => Fin.cons ((A.col i) j) (A j)).det = 0 := by
  refine Matrix.det_zero_of_column_eq (i := (0 : Fin (m+1))) (j := Fin.succ i) ?_ ?_
  · exact (Fin.succ_ne_zero i).symm
  · intro k
    simp [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Matrix.col_apply]

/-- The cofactor vector is orthogonal to every column of the matrix. -/
theorem inner_colVec_cofactorVec_aux {m : ℕ} (T : Amb m →L[ℝ] Tgt m) (i : Fin m) :
    inner ℝ (cofactorColVec (cofactorMatrix T) i) (cofactorVec T) = 0 := by
  rw [cofactorColVec, inner_cofactorVec_toLp_aux]
  exact det_prependCol_col_aux (cofactorMatrix T) i

/-- Coordinates of `T` in the standard basis: `(T x) i = ∑ j, A j i * x j`. -/
theorem T_apply_eq_sum_aux {m : ℕ} (T : Amb m →L[ℝ] Tgt m) (x : Amb m) (i : Fin m) :
    T x i = ∑ j : Fin (m+1), cofactorMatrix T j i * x j := by
  have hvec : x = ∑ j : Fin (m+1), x j • EuclideanSpace.single j 1 := by
    conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin (m+1))).sum_repr x]
    simp [PiLp.basisFun_repr, PiLp.basisFun_apply]
  have h1 : T x = ∑ j : Fin (m+1), x j • T (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hvec]
    rw [map_sum]
    simp
  have h2 : WithLp.ofLp (T x)
      = ∑ j : Fin (m+1), x j • WithLp.ofLp (T (EuclideanSpace.single j 1)) := by
    rw [h1, WithLp.ofLp_sum]
    simp [WithLp.ofLp_smul]
  change WithLp.ofLp (T x) i = ∑ j : Fin (m+1), cofactorMatrix T j i * x j
  rw [h2]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cofactorMatrix]
  ring

/-- The `i`-th coordinate functional of `T` is the inner product with the `i`-th column of `A`
(up to the identification `ℝ^m ↪ ℝ^{m+1}`). -/
theorem inner_colVec_eq_T_aux {m : ℕ} (T : Amb m →L[ℝ] Tgt m) (x : Amb m) (i : Fin m) :
    inner ℝ (cofactorColVec (cofactorMatrix T) i) x = T x i := by
  rw [cofactorColVec, PiLp.inner_apply, T_apply_eq_sum_aux]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply]
  exact mul_comm _ _

/-- Transporting the span of the columns of `A` from the function space `Fin (m+1) → ℝ` to the
Euclidean space `Amb m`. -/
theorem span_colVec_eq_comap_aux {m : ℕ} (A : Matrix (Fin (m+1)) (Fin m) ℝ) :
    Submodule.span ℝ (Set.range (cofactorColVec A))
      = Submodule.comap (WithLp.linearEquiv 2 ℝ (Fin (m+1) → ℝ)).toLinearMap
          (Submodule.span ℝ (Set.range A.col)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro u ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro x hx
    rw [Submodule.mem_comap] at hx
    have hmap : Submodule.map (WithLp.linearEquiv 2 ℝ (Fin (m+1) → ℝ)).symm.toLinearMap
        (Submodule.span ℝ (Set.range A.col)) ≤ Submodule.span ℝ (Set.range (cofactorColVec A)) := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨k, rfl⟩ := hi
      exact ⟨k, rfl⟩
    exact hmap ⟨(WithLp.linearEquiv 2 ℝ (Fin (m+1) → ℝ)) x, hx, rfl⟩

theorem ker_eq_span_cofactorVec {m : ℕ} (T : Work.Drive.Amb m →L[ℝ] Work.Drive.Tgt m)
    (hT : Function.Surjective T) :
    LinearMap.ker (T : Work.Drive.Amb m →ₗ[ℝ] Work.Drive.Tgt m) =
      Submodule.span ℝ {Work.Drive.cofactorVec T} := by
  classical
  have hA : LinearIndependent ℝ (cofactorMatrix T).col :=
    linearIndependent_cols_cofactorMatrix T hT
  -- the kernel is the orthogonal complement of the span of the columns of the matrix
  have h1' : ∀ x : Amb m, T x = 0 ↔
      x ∈ (Submodule.span ℝ (Set.range (cofactorColVec (cofactorMatrix T))))ᗮ := by
    intro x
    rw [Submodule.span_range_eq_iSup, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    constructor
    · intro hx i
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ?_
      rw [inner_colVec_eq_T_aux]
      exact congrArg (fun y : Tgt m => y i) hx
    · intro hx
      rw [← WithLp.ofLp_eq_zero, funext_iff]
      intro i
      rw [Pi.zero_apply]
      simpa only [inner_colVec_eq_T_aux] using
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hx i))
  have h1 : LinearMap.ker (T : Amb m →ₗ[ℝ] Tgt m)
      = (Submodule.span ℝ (Set.range (cofactorColVec (cofactorMatrix T))))ᗮ := by
    ext x
    rw [LinearMap.mem_ker]
    exact h1' x
  -- the span of the columns is the orthogonal complement of the cofactor vector
  have h2 : Submodule.span ℝ (Set.range (cofactorColVec (cofactorMatrix T)))
      = (Submodule.span ℝ ({cofactorVec T} : Set (Amb m)))ᗮ := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro u ⟨i, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (inner_colVec_cofactorVec_aux T i)
    · intro x hx
      have hx' : inner ℝ x (cofactorVec T) = 0 := by
        rw [real_inner_comm]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hx
      have hdet : (Matrix.of fun j => Fin.cons ((WithLp.ofLp x) j) (cofactorMatrix T j)).det = 0 := by
        rw [← inner_cofactorVec_toLp_aux T (WithLp.ofLp x), WithLp.toLp_ofLp]
        exact hx'
      rw [span_colVec_eq_comap_aux (cofactorMatrix T), Submodule.mem_comap]
      exact (det_prependCol_eq_zero_iff_mem_span (cofactorMatrix T) hA (WithLp.ofLp x)).mp hdet
  rw [h1, h2, Submodule.orthogonal_orthogonal]

end

end Work.Drive
