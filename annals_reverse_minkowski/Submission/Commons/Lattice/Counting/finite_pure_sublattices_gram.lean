import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq
import Submission.Commons.LinearAlgebra.Matrix.span_eq_of_minors_eq
import Submission.Commons.LinearAlgebra.Matrix.det_map_int_real
import Submission.Commons.LinearAlgebra.Matrix.exists_det_ne_zero_of_rank_ge
import Submission.Commons.LinearAlgebra.Matrix.linearIndependent_rat_of_int
import Submission.Commons.Lattice.Counting.mem_sat_iff_mem_qspan
import Submission.Commons.LinearAlgebra.Matrix.cols_linearIndependent_of_exists_submatrix_det_ne_zero
import Submission.Commons.LinearAlgebra.Matrix.det_ne_zero_of_cols_linearIndependent
import Submission.Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent

open Module
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Lattice.Counting

abbrev E (n : ℕ) := Fin n → ℤ
abbrev Q (n : ℕ) := Fin n → ℚ

/-- Coefficient-wise inclusion of the integer lattice into the rational vector space. -/
def toQMap (n : ℕ) : E n →ₗ[ℤ] Q n where
  toFun := fun x => fun i => (x i : ℚ)
  map_add' := by
    intro x y
    ext i
    simp
  map_smul' := by
    intro a x
    ext i
    simp [Pi.smul_apply]

@[simp]
lemma toQMap_apply (n : ℕ) (x : E n) (i : Fin n) : (toQMap n x) i = (x i : ℚ) := rfl

lemma toQMap_injective (n : ℕ) : Function.Injective (toQMap n) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- A submodule is pure (saturated): any vector becoming an element after multiplication
by a nonzero scalar already lies in it. -/
def Pure {n : ℕ} (M : Submodule ℤ (E n)) : Prop :=
  ∀ x : E n, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ M) → x ∈ M

/-- The integer matrix whose columns are the vectors `w j`. -/
def famMatrix {n r : ℕ} (w : Fin r → E n) : Matrix (Fin n) (Fin r) ℤ :=
  fun i j => w j i

lemma famMatrix_col {n r : ℕ} (w : Fin r → E n) (j : Fin r) : (famMatrix w).col j = w j := by
  funext i
  simp [famMatrix, Matrix.col_apply]

/-- A pure submodule containing the span of `w` consists exactly of the saturated vectors. -/
lemma mem_sat_of_span {n r : ℕ} {M : Submodule ℤ (E n)} (w : Fin r → E n)
    (hp : Pure M) (hspan : M = Submodule.span ℤ (Set.range w)) (x : E n) :
    x ∈ M ↔ ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Submodule.span ℤ (Set.range w) := by
  constructor
  · intro hx
    refine ⟨1, by norm_num, ?_⟩
    simpa [hspan] using hx
  · rintro ⟨a, ha, hax⟩
    exact hp x ⟨a, ha, by simpa [hspan] using hax⟩

section BasisValues

variable {n r : ℕ} {M : Submodule ℤ (E n)}

/-- The inclusion of a submodule into the ambient lattice (a `ℤ`-linear map). -/
def subtypeMap {n : ℕ} {M : Submodule ℤ (E n)} : M →ₗ[ℤ] E n where
  toFun := fun x => (x : E n)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

/-- Expanding an element of `M` in the basis `b` and casting to the ambient lattice. -/
lemma basis_expand (b : Basis (Fin r) ℤ M) (m : M) :
    (m : E n) = ∑ i : Fin r, (b.equivFun m i) • (b i : E n) := by
  calc
    (m : E n) = subtypeMap m := rfl
    _ = subtypeMap (b.equivFun.symm (b.equivFun m)) := by
      rw [b.equivFun.symm_apply_apply m]
    _ = subtypeMap (∑ i : Fin r, (b.equivFun m i) • b i) := by
      rw [b.equivFun_symm_apply]
    _ = ∑ i : Fin r, (b.equivFun m i) • subtypeMap (b i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
    _ = ∑ i : Fin r, (b.equivFun m i) • (b i : E n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rfl

/-- The ambient values of a `ℤ`-basis of a submodule of the integer lattice span the
submodule. -/
lemma basisValues_span (b : Basis (Fin r) ℤ M) :
    M = Submodule.span ℤ (Set.range (fun j : Fin r => (b j : E n))) := by
  apply le_antisymm
  · intro x hx
    let m : M := ⟨x, hx⟩
    have he := basis_expand b m
    change (↑m : E n) ∈ Submodule.span ℤ (Set.range fun j : Fin r => (b j : E n))
    rw [he]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact (b j).2

/-- The ambient values of a basis of a submodule of the integer lattice are `ℤ`-linearly
independent. -/
lemma basisValues_linearIndependent (b : Basis (Fin r) ℤ M) :
    LinearIndependent ℤ (fun j : Fin r => (b j : E n)) := by
  exact LinearIndependent.map' b.linearIndependent (subtypeMap) (Submodule.ker_subtype M)

end BasisValues

section QSpanBridge

/-- Rational span of a family of integer vectors (coefficient-wise cast into `ℚ`). -/
def qspan {n r : ℕ} (w : Fin r → E n) : Submodule ℚ (Q n) :=
  Submodule.span ℚ (Set.range (fun j : Fin r => fun i : Fin n => ((w j i : ℤ) : ℚ)))

/-- A pure submodule `M` with basis values `v` is determined by the rational span of `v`:
an element lies in `M` iff its cast lies in `qspan v`. -/
lemma pure_mem_iff_qspan {n r : ℕ} {M : Submodule ℤ (E n)} (b : Basis (Fin r) ℤ M)
    (hp : Pure M) (x : E n) :
    x ∈ M ↔ (fun i : Fin n => ((x : E n) i : ℚ)) ∈ qspan (fun j : Fin r => (b j : E n)) := by
  calc
    x ∈ M ↔ ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Submodule.span ℤ (Set.range (fun j : Fin r => (b j : E n))) :=
      mem_sat_of_span (w := fun j : Fin r => (b j : E n)) hp (basisValues_span b) x
    _ ↔ (fun i : Fin n => ((x : E n) i : ℚ)) ∈ qspan (fun j : Fin r => (b j : E n)) := by
      simpa [qspan] using (mem_sat_iff_mem_qspan (w := fun j : Fin r => (b j : E n)) x)

/-- Two pure submodules whose (basis-value) rational spans agree are equal. -/
lemma pure_eq_of_qspan_eq {n r : ℕ} {M M' : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) (b' : Basis (Fin r) ℤ M') (hp : Pure M) (hp' : Pure M')
    (hspanQ : qspan (fun j : Fin r => (b j : E n)) = qspan (fun j : Fin r => (b' j : E n))) :
    M = M' := by
  apply le_antisymm
  · intro x hx
    exact (pure_mem_iff_qspan b' hp' x).2 (by
      simpa [hspanQ] using (pure_mem_iff_qspan b hp x).1 hx)
  · intro x hx
    exact (pure_mem_iff_qspan b hp x).2 (by
      simpa [← hspanQ] using (pure_mem_iff_qspan b' hp' x).1 hx)

end QSpanBridge

section MatrixBounds

open Matrix

/-- Submatrix (rows `e`, all columns) commutes with multiplication on the right by a
square matrix `U` (acting on the columns). -/
lemma submatrix_mul_cols {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℤ) (U : Matrix (Fin r) (Fin r) ℤ)
    (e : Fin r ↪ Fin n) :
    ((V * U).submatrix e (fun j : Fin r => j)) = (V.submatrix e (fun j : Fin r => j)) * U := by
  ext i k
  calc
    ((V * U).submatrix e (fun j : Fin r => j)) i k = (V * U) (e i) k := rfl
    _ = ∑ j : Fin r, V (e i) j * U j k := by simp [Matrix.mul_apply]
    _ = ∑ j : Fin r, (V.submatrix e (fun j : Fin r => j)) i j * U j k := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Matrix.submatrix_apply]
    _ = ((V.submatrix e (fun j : Fin r => j)) * U) i k := by simp [Matrix.mul_apply]

/-- Determinant of an `r × r` minor of a product `V * U` (rows selected by `e`) is the
product of the corresponding minor of `V` and the determinant of `U`. -/
lemma minor_det_mul {n r : ℕ} (V : Matrix (Fin n) (Fin r) ℤ) (U : Matrix (Fin r) (Fin r) ℤ)
    (e : Fin r ↪ Fin n) :
    det ((V * U).submatrix e (fun j : Fin r => j)) =
      det (V.submatrix e (fun j : Fin r => j)) * U.det := by
  rw [submatrix_mul_cols V U e, Matrix.det_mul]

/-- Absolute value bound on the determinant of any `r × r` minor of an integer matrix
whose Gram determinant is at most `B ≥ 0`. -/
lemma abs_minor_det_le_sqrt_gram {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ) {B : ℝ} (hB : 0 ≤ B)
    (e : Fin r ↪ Fin n)
    (hgram : (((A.map (fun z : ℤ => (z : ℝ))).transpose *
        (A.map (fun z : ℤ => (z : ℝ)))).det) ≤ B) :
    |((det (A.submatrix e (fun j : Fin r => j)) : ℤ) : ℝ)| ≤ Real.sqrt B := by
  let X : Matrix (Fin r) (Fin r) ℤ := A.submatrix e (fun j : Fin r => j)
  let z : ℤ := det X
  have h1 := Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq A e
  have hreal : (z : ℝ) = det (X.map (fun z : ℤ => (z : ℝ))) := by
    simpa [X, z] using (Commons.LinearAlgebra.Matrix.det_map_int_real X).symm
  have hsq : (z : ℝ) ^ 2 ≤ B := by
    calc
      (z : ℝ) ^ 2 = (det (X.map (fun z : ℤ => (z : ℝ)))) ^ 2 := by rw [hreal]
      _ = (det ((A.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).map (fun z : ℤ => (z : ℝ)))) ^ 2 := by
            simp [X]
      _ ≤ (((A.map (fun z : ℤ => (z : ℝ))).transpose * (A.map (fun z : ℤ => (z : ℝ)))).det) := h1
      _ ≤ B := hgram
  have hmain : |(z : ℝ)| ≤ Real.sqrt B := by
    have hsq2 : (z : ℝ) ^ 2 ≤ (Real.sqrt B) ^ 2 := by
      simpa [Real.sq_sqrt hB] using hsq
    exact abs_le_of_sq_le_sq hsq2 (Real.sqrt_nonneg B)
  simpa [z] using hmain

/-- The coordinate matrix expressing the columns of `A` in the basis of `M`. -/
def coordMatrix {n r : ℕ} {M : Submodule ℤ (E n)} (b : Basis (Fin r) ℤ M)
    (A : Matrix (Fin n) (Fin r) ℤ) (hAcol : ∀ j : Fin r, A.col j ∈ M) :
    Matrix (Fin r) (Fin r) ℤ :=
  fun i j => b.equivFun (⟨A.col j, hAcol j⟩ : M) i

/-- Columns of `A` lie in `M`, `V` is the basis matrix of `M`: then `A = V * U`. -/
lemma matrix_eq_basis_mul_coords {n r : ℕ} {M : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) (A : Matrix (Fin n) (Fin r) ℤ)
    (hAcol : ∀ j : Fin r, A.col j ∈ M) :
    A = famMatrix (fun j : Fin r => (b j : E n)) * coordMatrix b A hAcol := by
  ext i j
  let U : Matrix (Fin r) (Fin r) ℤ := coordMatrix b A hAcol
  have hcol : A.col j = ∑ k : Fin r, U k j • (b k : E n) := by
    have he := basis_expand b (⟨A.col j, hAcol j⟩ : M)
    change ((⟨A.col j, hAcol j⟩ : M) : E n) = ∑ i : Fin r, (b.equivFun (⟨A.col j, hAcol j⟩ : M) i) • (b i : E n) at he
    simpa [U, coordMatrix] using he
  calc
    A i j = (A.col j) i := by simp [Matrix.col_apply]
    _ = (∑ k : Fin r, U k j • (b k : E n)) i := by rw [hcol]
    _ = ∑ k : Fin r, U k j * (b k : E n) i := by simp [Finset.sum_apply]
    _ = (famMatrix (fun j : Fin r => (b j : E n)) * U) i j := by
      simp [famMatrix, Matrix.mul_apply, mul_comm]
    _ = (famMatrix (fun j : Fin r => (b j : E n)) * coordMatrix b A hAcol) i j := by
      rfl

/-- The coordinate vectors of a linearly independent family (in a basis) are linearly
independent. -/
lemma linearIndependent_coords {n r : ℕ} {M : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) {w : Fin r → E n}
    (hw : ∀ j : Fin r, w j ∈ M) (hind : LinearIndependent ℤ w) :
    LinearIndependent ℤ (fun j : Fin r => b.equivFun (⟨w j, hw j⟩ : M)) := by
  classical
  let mj : Fin r → M := fun j => ⟨w j, hw j⟩
  have hmjind : LinearIndependent ℤ mj := by
    rw [Fintype.linearIndependent_iff] at hind
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    apply hind c ?_ j
    have hE : M.subtype (∑ j : Fin r, c j • mj j) = 0 := by
      rw [hc]
      exact map_zero M.subtype
    rw [map_sum] at hE
    simpa [mj, Finset.sum_apply] using hE
  let f : M →ₗ[ℤ] (Fin r → ℤ) := b.equivFun.toLinearMap
  have hker : f.ker = ⊥ := (LinearMap.ker_eq_bot).mpr b.equivFun.injective
  have hf : LinearIndependent ℤ (fun j : Fin r => f (mj j)) :=
    LinearIndependent.map' hmjind f hker
  simpa [mj, f, Function.comp_def] using hf

/-- The columns of the coordinate matrix are the coordinate vectors, hence linearly
independent whenever the columns of `A` are. -/
lemma coordMatrix_cols_linearIndependent {n r : ℕ} {M : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) (A : Matrix (Fin n) (Fin r) ℤ)
    (hAcol : ∀ j : Fin r, A.col j ∈ M) (hind : LinearIndependent ℤ A.col) :
    LinearIndependent ℤ (coordMatrix b A hAcol).col := by
  have h := linearIndependent_coords (b := b) (w := A.col) hAcol hind
  change LinearIndependent ℤ (fun j : Fin r => b.equivFun (⟨A.col j, hAcol j⟩ : M))
  exact h

end MatrixBounds

section BoundBasisMinors

open Matrix

/-- If `M` admits a basis `b` and a witness `A` (columns in `M`, some full-rank minor,
Gram determinant ≤ `B ≥ 0`), then every minor of the basis matrix of `M` is bounded by
`√B`. -/
lemma basis_minors_le_of_witness {n r : ℕ} {M : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) {B : ℝ} (hB : 0 ≤ B)
    (A : Matrix (Fin n) (Fin r) ℤ)
    (hAcol : ∀ j : Fin r, A.col j ∈ M)
    (hfull : ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0)
    (hgram : (((A.map (fun z : ℤ => (z : ℝ))).transpose * (A.map (fun z : ℤ => (z : ℝ)))).det) ≤ B)
    (e : Fin r ↪ Fin n) :
    |((det ((famMatrix (fun j : Fin r => (b j : E n))).submatrix e (fun j : Fin r => j)) : ℤ) : ℝ)| ≤
      Real.sqrt B := by
  let V : Matrix (Fin n) (Fin r) ℤ := famMatrix (fun j : Fin r => (b j : E n))
  let U : Matrix (Fin r) (Fin r) ℤ := coordMatrix b A hAcol
  have hAind : LinearIndependent ℤ A.col :=
    Commons.LinearAlgebra.Matrix.cols_linearIndependent_of_exists_submatrix_det_ne_zero A hfull
  have hAU : A = V * U := by
    simpa [V, U] using (matrix_eq_basis_mul_coords b A hAcol)
  have hUind : LinearIndependent ℤ U.col := coordMatrix_cols_linearIndependent b A hAcol hAind
  have hUdet : U.det ≠ 0 :=
    Commons.LinearAlgebra.Matrix.det_ne_zero_of_cols_linearIndependent U hUind
  -- relation between the minors of A and of the basis matrix:
  have hminor : det (A.submatrix e (fun j : Fin r => j)) =
      det ((famMatrix (fun j : Fin r => (b j : E n))).submatrix e (fun j : Fin r => j)) * U.det := by
    rw [hAU]
    simpa [V] using (minor_det_mul (V := V) (U := U) e)
  have hbA : |((det (A.submatrix e (fun j : Fin r => j)) : ℤ) : ℝ)| ≤ Real.sqrt B :=
    abs_minor_det_le_sqrt_gram A hB e hgram
  let zV : ℤ := det ((famMatrix (fun j : Fin r => (b j : E n))).submatrix e (fun j : Fin r => j))
  let zA : ℤ := det (A.submatrix e (fun j : Fin r => j))
  let dU : ℤ := U.det
  have hrel : (zA : ℝ) = (zV : ℝ) * (dU : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) hminor
    dsimp [zV, zA, dU] at h ⊢
    rw [Int.cast_mul] at h
    exact h
  have habs : |(zA : ℝ)| = |(zV : ℝ)| * |(dU : ℝ)| := by
    rw [hrel, abs_mul]
  have hdU1 : (1 : ℝ) ≤ |(dU : ℝ)| := by
    have hdabs : (1 : ℤ) ≤ |dU| := Int.one_le_abs hUdet
    have hcast : |(dU : ℝ)| = ((|dU| : ℤ) : ℝ) := (Int.cast_abs (R := ℝ)).symm
    rw [hcast]
    exact_mod_cast hdabs
  have hnonneg : 0 ≤ |(zV : ℝ)| := abs_nonneg _
  have hzVle : |(zV : ℝ)| ≤ |(zA : ℝ)| := by
    calc
      |(zV : ℝ)| = |(zV : ℝ)| * (1 : ℝ) := by rw [mul_one]
      _ ≤ |(zV : ℝ)| * |(dU : ℝ)| := by
        exact mul_le_mul_of_nonneg_left hdU1 hnonneg
      _ = |(zA : ℝ)| := habs.symm
  have hzV : |(zV : ℝ)| ≤ Real.sqrt B := by
    exact le_trans hzVle hbA
  simpa [zV] using hzV

end BoundBasisMinors

section MinorsInjection

open Matrix

/-- Two pure submodules whose basis matrices have identical integer minors coincide. -/
lemma pure_eq_of_minors_eq {n r : ℕ} {M M' : Submodule ℤ (E n)}
    (b : Basis (Fin r) ℤ M) (b' : Basis (Fin r) ℤ M') (hp : Pure M) (hp' : Pure M')
    (hmin : ∀ e : Fin r ↪ Fin n,
      det ((famMatrix (fun j : Fin r => (b j : E n))).submatrix e (fun j : Fin r => j)) =
      det ((famMatrix (fun j : Fin r => (b' j : E n))).submatrix e (fun j : Fin r => j))) :
    M = M' := by
  classical
  let v : Fin r → E n := fun j : Fin r => (b j : E n)
  let v' : Fin r → E n := fun j : Fin r => (b' j : E n)
  let V : Matrix (Fin n) (Fin r) ℤ := famMatrix v
  let V' : Matrix (Fin n) (Fin r) ℤ := famMatrix v'
  let VQ : Matrix (Fin n) (Fin r) ℚ := V.map (fun z : ℤ => (z : ℚ))
  let VQ' : Matrix (Fin n) (Fin r) ℚ := V'.map (fun z : ℤ => (z : ℚ))
  have hminQ : ∀ e : Fin r ↪ Fin n,
      det (VQ.submatrix e (fun j : Fin r => j)) = det (VQ'.submatrix e (fun j : Fin r => j)) := by
    intro e
    have hmap : (V.submatrix e (fun j : Fin r => j)).map (fun z : ℤ => (z : ℚ)) =
        VQ.submatrix e (fun j : Fin r => j) := by
      simpa [VQ] using (Matrix.submatrix_map (fun z : ℤ => (z : ℚ)) e (fun j : Fin r => j) V).symm
    have hmap' : (V'.submatrix e (fun j : Fin r => j)).map (fun z : ℤ => (z : ℚ)) =
        VQ'.submatrix e (fun j : Fin r => j) := by
      simpa [VQ'] using (Matrix.submatrix_map (fun z : ℤ => (z : ℚ)) e (fun j : Fin r => j) V').symm
    calc
      det (VQ.submatrix e (fun j : Fin r => j))
          = det ((V.submatrix e (fun j : Fin r => j)).map (fun z : ℤ => (z : ℚ))) := by rw [hmap]
      _ = ((det (V.submatrix e (fun j : Fin r => j)) : ℤ) : ℚ) := by
            exact (Int.cast_det (R := ℚ) (V.submatrix e (fun j : Fin r => j))).symm
      _ = ((det (V'.submatrix e (fun j : Fin r => j)) : ℤ) : ℚ) := by
            rw [hmin e]
      _ = det ((V'.submatrix e (fun j : Fin r => j)).map (fun z : ℤ => (z : ℚ))) := by
            exact (Int.cast_det (R := ℚ) (V'.submatrix e (fun j : Fin r => j)))
      _ = det (VQ'.submatrix e (fun j : Fin r => j)) := by rw [hmap']
  have hVcol : V.col = fun j : Fin r => (b j : E n) := by
    funext j
    exact famMatrix_col v j
  have hfull : ∃ e : Fin r ↪ Fin n, (V.submatrix e (fun j : Fin r => j)).det ≠ 0 := by
    have hind : LinearIndependent ℤ V.col := by
      rw [hVcol]
      exact basisValues_linearIndependent b
    exact Commons.LinearAlgebra.Matrix.exists_submatrix_det_ne_zero_of_cols_linearIndependent V hind
  have hfullQ : ∃ e : Fin r ↪ Fin n, det (VQ.submatrix e (fun j : Fin r => j)) ≠ 0 := by
    rcases hfull with ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hcast : ((det (V.submatrix e (fun j : Fin r => j)) : ℤ) : ℚ) =
        det (VQ.submatrix e (fun j : Fin r => j)) := by
      dsimp [VQ]
      rw [Matrix.submatrix_map]
      exact Int.cast_det (V.submatrix e (fun j : Fin r => j))
    have hz0 : ((det (V.submatrix e (fun j : Fin r => j)) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast he
    rw [hcast] at hz0
    exact hz0
  have hspan := Commons.LinearAlgebra.Matrix.span_eq_of_minors_eq VQ VQ' hfullQ hminQ
  -- hspan : span ℚ (range VQ.col) = span ℚ (range VQ'.col)
  have hrange1 : Set.range (fun j : Fin r => fun i : Fin n => ((v j i : ℤ) : ℚ)) = Set.range VQ.col := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      ext i
      simp [VQ, V, v, famMatrix, Matrix.col_apply]
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      ext i
      simp [VQ, V, v, famMatrix, Matrix.col_apply]
  have hrange2 : Set.range (fun j : Fin r => fun i : Fin n => ((v' j i : ℤ) : ℚ)) = Set.range VQ'.col := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      ext i
      simp [VQ', V', v', famMatrix, Matrix.col_apply]
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      ext i
      simp [VQ', V', v', famMatrix, Matrix.col_apply]
  have h1 : qspan v = Submodule.span ℚ (Set.range VQ.col) := by
    dsimp [qspan]
    rw [hrange1]
  have h2 : qspan v' = Submodule.span ℚ (Set.range VQ'.col) := by
    dsimp [qspan]
    rw [hrange2]
  have hq : qspan v = qspan v' := by
    rw [h1, h2]
    exact hspan
  exact pure_eq_of_qspan_eq b b' hp hp' (by simpa [v, v'] using hq)

end MinorsInjection

section MainTheorem

open Matrix

/-- Every submodule of the integer lattice `ℤⁿ` has rank at most `n`. -/
lemma finrank_submodule_le (n : ℕ) (M : Submodule ℤ (E n)) : Module.finrank ℤ M ≤ n := by
  calc
    Module.finrank ℤ M ≤ Module.finrank ℤ (E n) := Submodule.finrank_le (s := M)
    _ = n := by
      rw [Module.finrank_pi]
      simp

/-- If `B < 1` no pure rank-`r` sublattice can carry a witness matrix with Gram
determinant `≤ B`: the witness would have a nonzero integer minor, whose square is `≥ 1`,
but also `≤ Gram(A) ≤ B < 1`. -/
lemma no_witness_of_B_lt_one {n r : ℕ} (B : ℝ) (hB : B < 1)
    (A : Matrix (Fin n) (Fin r) ℤ)
    (hfull : ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0)
    (hgram : (((A.map (fun z : ℤ => (z : ℝ))).transpose *
        (A.map (fun z : ℤ => (z : ℝ)))).det) ≤ B) : False := by
  classical
  rcases hfull with ⟨e, he⟩
  let z : ℤ := det (A.submatrix e (fun j : Fin r => j))
  have hz0 : z ≠ 0 := he
  have hzabs : |(z : ℝ)| = (z.natAbs : ℝ) := by
    have h1 := (Int.cast_abs (R := ℝ) (a := z)).symm
    -- h1 : |(z : ℝ)| = ↑|z|
    rw [h1, Int.abs_eq_natAbs]
    norm_num
  have hz1 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
    have hz1i : 1 ≤ z.natAbs ^ 2 := by
      have : 1 ≤ z.natAbs := by omega
      nlinarith
    rw [← sq_abs (a := (z : ℝ))]
    rw [hzabs]
    have hsq : ((z.natAbs : ℝ) ^ 2) = ((z.natAbs ^ 2 : ℕ) : ℝ) := by
      norm_num [Nat.cast_pow]
    rw [hsq]
    exact_mod_cast hz1i
  have hcast : ((det (A.submatrix e (fun j : Fin r => j)) : ℤ) : ℝ) =
      det ((A.submatrix e (fun j : Fin r => j)).map (fun w : ℤ => (w : ℝ))) := by
    exact (Int.cast_det (R := ℝ) (A.submatrix e (fun j : Fin r => j)))
  have h1 := Commons.LinearAlgebra.Matrix.gram_det_ge_submatrix_det_sq A e
  have hbig : (z : ℝ) ^ 2 ≤
      (((A.map (fun w : ℤ => (w : ℝ))).transpose * (A.map (fun w : ℤ => (w : ℝ)))).det) := by
    have h1' : ((A.submatrix e (fun j : Fin r => j)).map (fun w : ℤ => (w : ℝ))).det ^ 2 ≤
        (((A.map (fun w : ℤ => (w : ℝ))).transpose * (A.map (fun w : ℤ => (w : ℝ)))).det) := by
      simpa using h1
    calc
      (z : ℝ) ^ 2 = ((det (A.submatrix e (fun j : Fin r => j)) : ℤ) : ℝ) ^ 2 := by simp [z]
      _ = ((A.submatrix e (fun j : Fin r => j)).map (fun w : ℤ => (w : ℝ))).det ^ 2 := by rw [hcast]
      _ ≤ (((A.map (fun w : ℤ => (w : ℝ))).transpose * (A.map (fun w : ℤ => (w : ℝ)))).det) := h1'
  linarith

end MainTheorem

open Matrix

/-- Finiteness of the pure (saturated) rank-`r` sublattices of `ℤⁿ` admitting a
basis-like matrix of bounded Gram determinant: the input to every finite-search argument
in the counting arguments. -/
theorem finite_pure_sublattices_gram {n r : ℕ} (B : ℝ) :
    {M : Submodule ℤ (Fin n → ℤ) |
      Module.finrank ℤ M = r ∧
      (∀ x : Fin n → ℤ, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ M) → x ∈ M) ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ M) ∧
        (∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose *
            (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))}.Finite := by
  classical
  let S : Set (Submodule ℤ (E n)) := {M | Module.finrank ℤ M = r ∧ Pure M ∧
      (∃ A : Matrix (Fin n) (Fin r) ℤ,
        (∀ j : Fin r, (fun i => A i j) ∈ M) ∧
        (∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0) ∧
        (((A.map (fun z : ℤ => (z : ℝ))).transpose * (A.map (fun z : ℤ => (z : ℝ)))).det ≤ B))}
  change S.Finite
  by_cases hB : B < 1
  · have hS : S = ∅ := by
      ext M
      constructor
      · intro hM
        rcases hM with ⟨hfr, hp, hw⟩
        rcases hw with ⟨A, hAcol, hfull, hgram⟩
        exfalso
        exact no_witness_of_B_lt_one B hB A hfull hgram
      · intro hx
        simp at hx
    rw [hS]
    exact Set.finite_empty
  · have hB1 : 1 ≤ B := le_of_not_gt hB
    have hB0 : 0 ≤ B := by linarith
    by_cases hrn : n < r
    · have hS : S = ∅ := by
        ext M
        constructor
        · intro hM
          rcases hM with ⟨hfr, _⟩
          have hle : Module.finrank ℤ M ≤ n := finrank_submodule_le n M
          omega
        · intro hx
          simp at hx
      rw [hS]
      exact Set.finite_empty
    · let N : ℕ := Nat.ceil (Real.sqrt B)
      let Cod := ∀ e : Fin r ↪ Fin n, {z : ℤ // z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}
      haveI hCodFin : Finite Cod := by infer_instance
      let F : {M : Submodule ℤ (E n) // M ∈ S} → Cod := by
        intro ⟨M, hM⟩ e
        let bM : Basis (Fin r) ℤ M := Module.finBasisOfFinrankEq ℤ M hM.1
        let z : ℤ := det ((famMatrix (fun j : Fin r => (bM j : E n))).submatrix e (fun j : Fin r => j))
        refine ⟨z, ?_⟩
        rcases hM with ⟨hfr, hp, hw⟩
        rcases hw with ⟨A, hAcol, hfull, hgram⟩
        have hAcol' : ∀ j : Fin r, A.col j ∈ M := by
          intro j
          exact hAcol j
        have hN : Real.sqrt B ≤ (N : ℝ) := by exact Nat.le_ceil (Real.sqrt B)
        have hz : |((z : ℤ) : ℝ)| ≤ (N : ℝ) := by
          simpa [z] using (le_trans (basis_minors_le_of_witness bM hB0 A hAcol' hfull hgram e) hN)
        rw [Finset.mem_Icc]
        constructor
        · have hzge : -(N : ℝ) ≤ (z : ℝ) := (abs_le.mp hz).1
          exact_mod_cast hzge
        · have hzle : (z : ℝ) ≤ (N : ℝ) := (abs_le.mp hz).2
          exact_mod_cast hzle
      have hInj : Function.Injective F := by
        intro ⟨M1, h1⟩ ⟨M2, h2⟩ hF
        let b1 : Basis (Fin r) ℤ M1 := Module.finBasisOfFinrankEq ℤ M1 h1.1
        let b2 : Basis (Fin r) ℤ M2 := Module.finBasisOfFinrankEq ℤ M2 h2.1
        apply Subtype.ext
        apply pure_eq_of_minors_eq (b := b1) (b' := b2) h1.2.1 h2.2.1
        intro e
        change (F ⟨M1, h1⟩ e).1 = (F ⟨M2, h2⟩ e).1
        exact congrArg Subtype.val (congrFun hF e)
      haveI : Finite {M : Submodule ℤ (E n) // M ∈ S} := Finite.of_injective F hInj
      exact Set.toFinite S


end Commons.Lattice.Counting
