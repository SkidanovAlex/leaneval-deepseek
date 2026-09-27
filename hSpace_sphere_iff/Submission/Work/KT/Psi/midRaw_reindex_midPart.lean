import Mathlib
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

/-!
# `Work.KT.Psi.midRaw_reindex_midPart`

The "mixed" block of the block decomposition of `(p ⊕ q) ⊗ (p ⊕ q)` is written in
`Submission/Work/KT/Psi/psi2sum_Setup.lean` in two ways:

* `midRaw ε p q`, on the index set `(Fin p.1 × Fin q.1) ⊕ (Fin q.1 × Fin p.1)`, whose
  off-diagonal blocks `kronP p q * relMat A (Equiv.prodComm _ _)` are partial permutation
  matrices realising the swap of the two factors;
* `midPart ε p q`, on `(Fin p.1 × Fin q.1) ⊕ (Fin p.1 × Fin q.1)`, where the swap has been
  absorbed into the index set: the off-diagonal blocks are literally `kronP p q` again.

This file proves that the two descriptions agree:

`midRaw_reindex_midPart` — reindexing `midRaw ε p q` along
`Equiv.sumCongr (Equiv.refl _) (Equiv.prodComm _ _)` gives `midPart ε p q`, for a *commutative*
coefficient ring (`hA : ∀ x y, x * y = y * x`).  Commutativity of `A` is needed only to move
`kronP q p` to `kronP p q` in the bottom right block, i.e. to exchange the two tensor factors.

The proof is assembled from a small set of general reindexing identities for block matrices and
partial permutation matrices, which are stated here in the generality in which they are true and
may be imported by other parts of the development:

* `reindex_smul_gen` — reindexing commutes with a constant scalar multiple;
* `reindex_fromBlocks_sumCongr` — a `sumCongr` reindexing of a `2 × 2` block matrix acts
  blockwise;
* `reindex_refl_mul_relMat` — `X * relMat R g` is the reindexing of `X` by `g.symm` on columns;
* `reindex_mul_relMat_refl` — the same on rows;
* `reindex_prodComm_kroneckerMap` — over a commutative ring, `N ⊗ M` reindexed by `prodComm`
  is `M ⊗ N`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## General reindexing identities -/

/-- Reindexing a matrix commutes with multiplication by a constant scalar. -/
theorem reindex_smul_gen {R : Type} [Mul R] {ι κ ι' κ' : Type} (e : ι ≃ ι') (f : κ ≃ κ')
    (c : R) (X : Matrix ι κ R) : Matrix.reindex e f (c • X) = c • Matrix.reindex e f X := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]

/-- Reindexing a `2 × 2` block matrix along a `sumCongr` equivalence acts blockwise, the row
equivalence of each block being the one for its row component and likewise for columns. -/
theorem reindex_fromBlocks_sumCongr {R : Type} [Zero R] {n l o m n' l' o' m' : Type}
    (e₁ : n ≃ n') (f₁ : l ≃ l') (e₂ : o ≃ o') (f₂ : m ≃ m')
    (B₁ : Matrix n l R) (B₂ : Matrix n m R) (B₃ : Matrix o l R) (B₄ : Matrix o m R) :
    Matrix.reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr f₁ f₂)
        (Matrix.fromBlocks B₁ B₂ B₃ B₄) =
      Matrix.fromBlocks (Matrix.reindex e₁ f₁ B₁) (Matrix.reindex e₁ f₂ B₂)
        (Matrix.reindex e₂ f₁ B₃) (Matrix.reindex e₂ f₂ B₄) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Multiplying a matrix on the right by the partial permutation matrix `relMat R g` reindexes
its columns by `g`; expressed the other way round, reindexing the columns by `g.symm` recovers
`X` itself. -/
theorem reindex_refl_mul_relMat {R : Type} [Ring R] {ι μ ν : Type} [Fintype μ] [DecidableEq ν]
    (g : μ ≃ ν) (X : Matrix ι μ R) :
    Matrix.reindex (Equiv.refl ι) g.symm (X * relMat R g) = X := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.refl_symm, Equiv.symm_symm, Matrix.mul_apply, relMat]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (g.injective h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Multiplying a square matrix on the right by `relMat R g` reindexes its index set; undoing
that reindexing on the columns gives the conjugation of `X` by `g`. -/
theorem reindex_mul_relMat_refl {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [DecidableEq κ]
    (f : ι ≃ κ) (X : Matrix ι ι R) :
    Matrix.reindex f (Equiv.refl κ) (X * relMat R f) = Matrix.reindex f f X := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.refl_symm, Equiv.refl_apply, Matrix.mul_apply, relMat]
  rw [Finset.sum_eq_single (f.symm j)]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb ((Equiv.eq_symm_apply f).mpr h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Over a commutative ring, reindexing the Kronecker product `N ⊗ M` along the swap of the two
factors gives `M ⊗ N`. -/
theorem reindex_prodComm_kroneckerMap {R : Type} [Ring R] (hR : ∀ x y : R, x * y = y * x)
    {α β : Type} (M : Matrix α α R) (N : Matrix β β R) :
    Matrix.reindex (Equiv.prodComm β α) (Equiv.prodComm β α)
        (Matrix.kroneckerMap (· * ·) N M) =
      Matrix.kroneckerMap (· * ·) M N := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply]
  exact hR _ _

/-! ## The mixed block -/

theorem midRaw_reindex_midPart {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ε : ℂ) (p q : Work.KT.Mat A) :
    Matrix.reindex (Equiv.sumCongr (Equiv.refl (Fin p.1 × Fin q.1)) (Equiv.prodComm (Fin q.1) (Fin p.1)))
        (Equiv.sumCongr (Equiv.refl (Fin p.1 × Fin q.1)) (Equiv.prodComm (Fin q.1) (Fin p.1)))
        (Work.KT.Psi.midRaw ε p q) = Work.KT.Psi.midPart ε p q := by
  -- The two index sets are `α ⊕ β` and `α ⊕ α` with `α = Fin p.1 × Fin q.1`, `β = Fin q.1 × Fin p.1`,
  -- and the reindexing is `sumCongr (refl α) σ` with `σ = (prodComm α β)⁻¹ = prodComm β α`.
  have hσ : Matrix.reindex (Equiv.prodComm (Fin p.1) (Fin q.1)).symm
      (Equiv.prodComm (Fin p.1) (Fin q.1)).symm (kronP q p) = kronP p q := by
    unfold kronP
    simp only [Equiv.prodComm_symm]
    exact reindex_prodComm_kroneckerMap hA p.2 q.2
  rw [midRaw, midPart]
  rw [Work.KT.reindex_smul]
  rw [reindex_fromBlocks_sumCongr]
  rw [reindex_smul_gen, reindex_smul_gen]
  rw [Matrix.reindex_refl_refl]
  -- rewrite the swapped factor `prodComm β α` as `(prodComm α β).symm`, the form in which the
  -- reindexing identities for `relMat` are stated
  rw [← Equiv.prodComm_symm (Fin p.1) (Fin q.1)]
  -- top right: `kronP p q * relMat A (prodComm α β)` reindexed on the columns is `kronP p q`;
  -- bottom left: the same block after the index swap is `kronP q p` reindexed by `prodComm`;
  -- bottom right: `kronP q p` reindexed by `prodComm` is `kronP p q` (commutativity of `A`).
  rw [reindex_refl_mul_relMat, reindex_mul_relMat_refl, hσ]

end

end Work.KT.Psi
