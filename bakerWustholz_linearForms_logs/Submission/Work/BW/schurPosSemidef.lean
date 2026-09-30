import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

/-!
# The Schur complement of a positive semidefinite block matrix

If the block matrix `[A₁₁ A₁₂; A₂₁ A₂₂]` is positive semidefinite and the top-left block `A₁₁`
is invertible, then the Schur complement `A₂₂ - A₂₁ A₁₁⁻¹ A₁₂` is positive semidefinite.

The proof is the standard one: a positive semidefinite matrix is Hermitian, so `A₂₁ = A₁₂ᴴ`;
the top-left block is a principal submatrix, hence positive semidefinite, and being invertible
as well it is positive definite; finally Mathlib's Schur complement criterion
`Matrix.PosDef.fromBlocks₁₁` applies.
-/

namespace Work.BW

/-- The principal submatrix of a block matrix `[A B; C D]` on the `inl` indices is the top-left
block `A`. -/
private lemma fromBlocks_submatrix_inl_inl {m n : Type*} {α : Type*}
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) :
    (Matrix.fromBlocks A B C D).submatrix (Sum.inl : m → m ⊕ n) Sum.inl = A := by
  ext i j
  simp [Matrix.submatrix_apply]

lemma schurPosSemidef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A₁₁ : Matrix m m ℝ} {A₁₂ : Matrix m n ℝ} {A₂₁ : Matrix n m ℝ} {A₂₂ : Matrix n n ℝ}
    [Invertible A₁₁]
    (h : (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).PosSemidef) :
    (A₂₂ - A₂₁ * ⅟A₁₁ * A₁₂).PosSemidef := by
  -- The block matrix is Hermitian, which yields `A₁₂ᴴ = A₂₁`.
  obtain ⟨-, hBC, -, -⟩ := Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian
  -- `A₁₁` is positive semidefinite as a principal submatrix of `h`, and invertible by
  -- hypothesis, hence positive definite.
  have hA₁₁psd : A₁₁.PosSemidef := by
    have hh := h.submatrix (Sum.inl : m → m ⊕ n)
    rwa [fromBlocks_submatrix_inl_inl A₁₁ A₁₂ A₂₁ A₂₂] at hh
  have hA₁₁pd : A₁₁.PosDef := (hA₁₁psd.posDef_iff_isUnit).mpr (isUnit_of_invertible A₁₁)
  -- Rewrite the off-diagonal block as `A₁₂ᴴ` and apply Mathlib's Schur complement criterion.
  have h' : (Matrix.fromBlocks A₁₁ A₁₂ A₁₂ᴴ A₂₂).PosSemidef := by
    rw [← hBC] at h
    exact h
  have key : (A₂₂ - A₁₂ᴴ * A₁₁⁻¹ * A₁₂).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ A₁₂ A₂₂ hA₁₁pd).mp h'
  rw [Matrix.invOf_eq_nonsing_inv]
  exact hBC.symm ▸ key

end Work.BW
