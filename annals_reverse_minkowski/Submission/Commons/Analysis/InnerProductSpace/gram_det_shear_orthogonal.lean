import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-! # Gram determinant of a family obtained by an orthogonal shear

Let `u : ι → E` be a family spanning `S = span (range u)`, and let `w : κ → E` be a
family orthogonal to `S`.  If each `x j - w j` lies in `S` (so `x` is obtained from `w`
by a shear in the direction of the `u`-family), then

    det (gram (Sum.elim u x)) = det (gram u) * det (gram w).

Two ingredients go in:

1. *Shear invariance.*  Replacing each `w j` by `x j = w j + (linear combination of the
   `u i`)` conjugates the Gram matrix by a unitriangular block matrix, so the determinant
   is unchanged.
2. *Block diagonalisation.*  Since `w` is orthogonal to the span of `u`, the Gram matrix
   of `Sum.elim u w` is block diagonal with blocks `gram u` and `gram w`.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `f a = ∑ b, M a b • g b`, then the Gram matrix of `f` is `M * gram g * Mᵀ`. -/
lemma gram_eq_mul_gram_mul_transpose {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (g : ι → E) :
    Matrix.gram ℝ (fun a => ∑ b, M a b • g b) = M * Matrix.gram ℝ g * Matrix.transpose M := by
  ext a c
  simp_rw [Matrix.gram_apply]
  rw [sum_inner Finset.univ]
  simp_rw [inner_sum Finset.univ]
  simp_rw [real_inner_smul_left, real_inner_smul_right]
  simp_rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, Matrix.gram_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  ac_rfl

/-- The Gram determinant of a family is unchanged if each vector of the second block is
replaced by itself plus an element of the span of the first block. -/
lemma gram_det_eq_of_span_diff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (u : ι → E) (x w : κ → E)
    (hxw : ∀ j, x j - w j ∈ Submodule.span ℝ (Set.range u)) :
    (Matrix.gram ℝ (Sum.elim u x)).det = (Matrix.gram ℝ (Sum.elim u w)).det := by
  classical
  have hcoeff : ∀ j, ∃ c : ι → ℝ, (∑ i, c i • u i) = x j - w j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hxw j)
  let c : κ → ι → ℝ := fun j i => Classical.choose (hcoeff j) i
  have hc : ∀ j, (∑ i, c j i • u i) = x j - w j := by
    intro j
    exact Classical.choose_spec (hcoeff j)
  let C : Matrix κ ι ℝ := Matrix.of fun j i => c j i
  let M : Matrix (Sum ι κ) (Sum ι κ) ℝ :=
    Matrix.fromBlocks (1 : Matrix ι ι ℝ) (0 : Matrix ι κ ℝ) C (1 : Matrix κ κ ℝ)
  have hfam : ∀ a, Sum.elim u x a = ∑ b, M a b • Sum.elim u w b := by
    intro a
    cases a with
    | inl k =>
      rw [Fintype.sum_sum_type]
      simp [M, Matrix.one_apply, Finset.sum_ite_eq]
    | inr j =>
      rw [Fintype.sum_sum_type]
      simp [M, C, Matrix.one_apply, Finset.sum_ite_eq]
      rw [hc j]
      simp
  have hgram : Matrix.gram ℝ (Sum.elim u x) =
      M * Matrix.gram ℝ (Sum.elim u w) * Matrix.transpose M := by
    have hfam' : (fun a : Sum ι κ => ∑ b, M a b • Sum.elim u w b) = Sum.elim u x := by
      funext a
      exact (hfam a).symm
    calc
      Matrix.gram ℝ (Sum.elim u x)
          = Matrix.gram ℝ (fun a : Sum ι κ => ∑ b, M a b • Sum.elim u w b) := by
            rw [hfam']
      _ = M * Matrix.gram ℝ (Sum.elim u w) * Matrix.transpose M :=
            gram_eq_mul_gram_mul_transpose M (Sum.elim u w)
  have hMdet : M.det = 1 := by
    simp [M]
  calc
    (Matrix.gram ℝ (Sum.elim u x)).det
        = (M * Matrix.gram ℝ (Sum.elim u w) * Matrix.transpose M).det := by rw [hgram]
    _ = (Matrix.gram ℝ (Sum.elim u w)).det := by
        rw [Matrix.det_mul, Matrix.det_mul]
        rw [Matrix.det_transpose, hMdet]
        ring

/-- The Gram determinant of the disjoint union of a family and a family orthogonal to its
span is the product of the two Gram determinants. -/
lemma gram_det_sum_elim_mul_of_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (u : ι → E) (w : κ → E)
    (hw : ∀ j, w j ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u))) :
    (Matrix.gram ℝ (Sum.elim u w)).det = (Matrix.gram ℝ u).det * (Matrix.gram ℝ w).det := by
  classical
  have hcross : ∀ i j, inner ℝ (u i) (w j) = 0 := by
    intro i j
    exact (Submodule.mem_orthogonal (Submodule.span ℝ (Set.range u)) (w j)).mp (hw j) (u i)
      (Submodule.subset_span (Set.mem_range_self i))
  have hgram : Matrix.gram ℝ (Sum.elim u w) =
      Matrix.fromBlocks (Matrix.gram ℝ u) 0 0 (Matrix.gram ℝ w) := by
    ext a c
    cases a <;> cases c <;> simp [hcross, real_inner_comm]
  calc
    (Matrix.gram ℝ (Sum.elim u w)).det
        = (Matrix.fromBlocks (Matrix.gram ℝ u) 0 0 (Matrix.gram ℝ w)).det := by rw [hgram]
    _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ w).det := by simp

/-- Generic form of `gram_det_shear_orthogonal`: the span condition is expressed directly
through the `u`-family rather than through an auxiliary submodule `S`. -/
lemma gram_det_shear_orthogonal_of_span {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (u : ι → E) (x w : κ → E)
    (hxw : ∀ j, x j - w j ∈ Submodule.span ℝ (Set.range u))
    (hw : ∀ j, w j ∈ Submodule.orthogonal (Submodule.span ℝ (Set.range u))) :
    (Matrix.gram ℝ (Sum.elim u x)).det = (Matrix.gram ℝ u).det * (Matrix.gram ℝ w).det := by
  rw [gram_det_eq_of_span_diff u x w hxw]
  exact gram_det_sum_elim_mul_of_orthogonal u w hw

end Commons.Analysis.InnerProductSpace

namespace Commons.Analysis.InnerProductSpace

/-- If `S` is spanned by the `u`-family and each `x j - w j` lies in `S` while each `w j`
is orthogonal to `S`, then the Gram determinant of `(u, x)` is the product of the Gram
determinants of `u` and `w`. -/
theorem gram_det_shear_orthogonal {N d r : ℕ}
    (u : Fin d → EuclideanSpace ℝ (Fin N)) (x w : Fin r → EuclideanSpace ℝ (Fin N))
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hS : S = Submodule.span ℝ (Set.range u))
    (hxw : ∀ j, x j - w j ∈ S)
    (hw : ∀ j, w j ∈ Submodule.orthogonal S) :
    (Matrix.gram ℝ (Sum.elim u x)).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ w).det := by
  classical
  refine gram_det_shear_orthogonal_of_span (ι := Fin d) (κ := Fin r)
    (E := EuclideanSpace ℝ (Fin N)) u x w ?_ ?_
  · intro j
    simpa [hS] using hxw j
  · intro j
    simpa [hS] using hw j

end Commons.Analysis.InnerProductSpace