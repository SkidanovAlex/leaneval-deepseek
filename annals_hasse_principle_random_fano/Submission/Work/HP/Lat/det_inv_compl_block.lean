import Mathlib

namespace Work.HP.Lat

open Matrix

set_option linter.style.haveILetI false

/-- Jacobi's complementary minor identity, at the level of `2×2` block matrices: if the top-left
block `A` and the whole matrix are invertible, then the bottom-right block of the inverse has
determinant `det A / det (fromBlocks A B C D)`. -/
lemma det_inv_fromBlocks₁₁ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    [Invertible A] [Invertible (D - C * ⅟A * B)] [Invertible (fromBlocks A B C D)] :
    ((fromBlocks A B C D)⁻¹).toBlocks₂₂.det = A.det / (fromBlocks A B C D).det := by
  rw [← invOf_eq_nonsing_inv (fromBlocks A B C D), invOf_fromBlocks₁₁_eq]
  rw [toBlocks_fromBlocks₂₂]
  rw [invOf_eq_nonsing_inv (D - C * ⅟A * B)]
  rw [det_nonsing_inv, Ring.inverse_eq_inv, det_fromBlocks₁₁]
  have hA0 : A.det ≠ 0 := ((isUnit_iff_isUnit_det A).mp (isUnit_of_invertible A)).ne_zero
  have hS0 : (D - C * ⅟A * B).det ≠ 0 :=
    ((isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)).ne_zero
  field_simp

/-- Jacobi's complementary minor identity, phrased for a matrix indexed by a sum type: the
determinant of the bottom-right block of the inverse is `det (top-left block) / det`. -/
lemma det_inv_toBlocks₂₂ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (N : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hN : N.det ≠ 0) (hA : N.toBlocks₁₁.det ≠ 0) :
    (N⁻¹).toBlocks₂₂.det = N.toBlocks₁₁.det / N.det := by
  set A := N.toBlocks₁₁ with hAdef
  set B := N.toBlocks₁₂ with hBdef
  set C := N.toBlocks₂₁ with hCdef
  set D := N.toBlocks₂₂ with hDdef
  have hNrep : fromBlocks A B C D = N := by
    rw [hAdef, hBdef, hCdef, hDdef]; exact fromBlocks_toBlocks N
  rw [← hNrep] at hN ⊢
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  haveI iA : Invertible A := invertibleOfIsUnitDet A hAu
  have hFBu : IsUnit (fromBlocks A B C D) :=
    (isUnit_iff_isUnit_det (fromBlocks A B C D)).mpr (isUnit_iff_ne_zero.mpr hN)
  haveI iFB : Invertible (fromBlocks A B C D) :=
    ((nonempty_invertible_iff_isUnit (fromBlocks A B C D)).mpr hFBu).some
  haveI iS : Invertible (D - C * ⅟A * B) :=
    ((nonempty_invertible_iff_isUnit (D - C * ⅟A * B)).mpr
      (isUnit_fromBlocks_iff_of_invertible₁₁.mp hFBu)).some
  exact det_inv_fromBlocks₁₁ A B C D

/-- Jacobi's complementary minor identity, block form: for an invertible matrix `M` and a predicate
`p` whose principal block `M[F,F]` is invertible, the complementary principal block of `M⁻¹` has
determinant `det M[F,F] / det M`. -/
theorem det_inv_compl_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) (p : ι → Prop) [DecidablePred p]
    (hA : (M.toSquareBlockProp p).det ≠ 0) :
    ((M⁻¹).toSquareBlockProp (fun i => ¬ p i)).det = (M.toSquareBlockProp p).det / M.det := by
  classical
  set N : Matrix ({i // p i} ⊕ {i // ¬p i}) ({i // p i} ⊕ {i // ¬p i}) ℝ :=
    reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm M with hNdef
  have hNdet : N.det = M.det := by rw [hNdef]; exact det_reindex_self _ _
  have h11 : N.toBlocks₁₁ = M.toSquareBlockProp p := by
    rw [hNdef]; ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toBlocks₁₁,
      Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.of_apply, Equiv.symm_symm,
      Equiv.sumCompl_apply_inl]
  have h22 : (N⁻¹).toBlocks₂₂ = (M⁻¹).toSquareBlockProp (fun i => ¬ p i) := by
    rw [hNdef, Matrix.inv_reindex]; ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toBlocks₂₂,
      Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.of_apply, Equiv.symm_symm,
      Equiv.sumCompl_apply_inr]
  have hN : N.det ≠ 0 := by rw [hNdet]; exact hM
  have hA' : N.toBlocks₁₁.det ≠ 0 := by rw [h11]; exact hA
  rw [← h22, ← h11, ← hNdet]
  exact det_inv_toBlocks₂₂ N hN hA'

end Work.HP.Lat
