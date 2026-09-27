import Mathlib
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.kappa_add_defs
import Submission.Work.KT.Fund.graphProj_block_defs
import Submission.Work.KT.Fund.graphProj_block_aux
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul

/-!
# `Work.KT.Fund.recipProj_blockB` — block decomposition of `recipProj`

`recipProj R G = orthProj R (recipB R G)` is the orthogonal projection onto the reciprocal graph
of `G`, `im [[G],[1]] ⊆ R^{2n}`.  The orthogonal projection onto the (reciprocal) graph of a
*block-diagonal* matrix is the block diagonal of the orthogonal projections of its blocks.
Concretely, for `G = G₁ ⊕ G₂` viewed as a matrix on `Fin (n + k)` through `finSumFinEquiv`,

`recipProj C(Y,ℂ) (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G₁ 0 0 G₂))`

equals `reindex (blkEquiv n k) (blkEquiv n k)` applied to the block-diagonal matrix with blocks
`recipProj C(Y,ℂ) G₁` and `recipProj C(Y,ℂ) G₂`.

The proof is purely algebraic.  Writing `Bᵢ = recipB R Gᵢ`, `f = finSumFinEquiv` and
`e = blkEquiv n k`,

* `recipB R (reindex f f (fromBlocks G₁ 0 0 G₂)) = reindex e f (fromBlocks B₁ 0 0 B₂)`, a
  combinatorial identity of index types (here `recipB_block_B`);
* `orthProj R` of a matrix of the shape `reindex e f (fromBlocks B₁ 0 0 B₂)` splits as
  `reindex e e (fromBlocks (orthProj R B₁) 0 0 (orthProj R B₂))`, because conjugation, matrix
  multiplication and `Ring.inverse` all respect reindexings, and the inverse of a block-diagonal
  matrix is block-diagonal (here `orthProj_reindex_blk_B`).

The helper lemmas below are `private` so that this file can be imported alongside
`Submission.Work.KT.Fund.recipProj_block` and `Submission.Work.KT.Fund.graphProj_block` without
duplicate declaration names.
-/

namespace Work.KT.Fund

open _root_.Matrix

/-- Reindexing commutes with the product of rectangular matrices. -/
private theorem reindex_mul_rectB {α : Type} [AddCommMonoid α] [Mul α]
    {l m n o p q : Type} [Fintype m] [Fintype n] [Fintype o]
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : m ≃ l) (e₂ : n ≃ o) (e₃ : p ≃ q) :
    Matrix.reindex e₁ e₃ (M * N) = Matrix.reindex e₁ e₂ M * Matrix.reindex e₂ e₃ N := by
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv M N e₁.symm e₂.symm e₃.symm]

/-- `Ring.inverse` of a reindexed square matrix, in the form needed below. -/
private theorem ringInverse_reindexB {R : Type} [CommRing R] {n m : Type} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m) (A : Matrix n n R) :
    Ring.inverse (Matrix.reindex e e A) = Matrix.reindex e e (Ring.inverse A) :=
  Matrix.ringInverse_reindex e A

/-- `orthProj` of a matrix which is a block diagonal in the `Fin n` and `Fin k` blocks (viewed
through `blkEquiv n k` and `finSumFinEquiv`) is the block diagonal of the `orthProj`s of the
blocks. -/
private theorem orthProj_reindex_blkB {R : Type} [CommRing R] [StarRing R] {n k : ℕ}
    (B₁ : Matrix (Fin n ⊕ Fin n) (Fin n) R) (B₂ : Matrix (Fin k ⊕ Fin k) (Fin k) R)
    (h₁ : IsUnit (B₁ᴴ * B₁)) (h₂ : IsUnit (B₂ᴴ * B₂)) :
    orthProj R (Matrix.reindex (blkEquiv n k) finSumFinEquiv (Matrix.fromBlocks B₁ 0 0 B₂))
      = Matrix.reindex (blkEquiv n k) (blkEquiv n k)
          (Matrix.fromBlocks (orthProj R B₁) 0 0 (orthProj R B₂)) := by
  set e : (Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k) ≃ Fin (n + k) ⊕ Fin (n + k) := blkEquiv n k with he
  set M : Matrix ((Fin n ⊕ Fin n) ⊕ (Fin k ⊕ Fin k)) (Fin n ⊕ Fin k) R :=
    Matrix.fromBlocks B₁ 0 0 B₂ with hM
  have hconj : Mᴴ = Matrix.fromBlocks B₁ᴴ 0 0 B₂ᴴ := by
    rw [hM, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
  have hMM : Mᴴ * M = Matrix.fromBlocks (B₁ᴴ * B₁) 0 0 (B₂ᴴ * B₂) := by
    rw [hconj, hM, Matrix.fromBlocks_multiply]; simp
  have hgr : (Matrix.reindex e finSumFinEquiv M)ᴴ * (Matrix.reindex e finSumFinEquiv M)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (B₁ᴴ * B₁) 0 0 (B₂ᴴ * B₂)) := by
    rw [Matrix.conjTranspose_reindex,
      ← reindex_mul_rectB Mᴴ M finSumFinEquiv e finSumFinEquiv, hMM]
  have hinv : Ring.inverse
        ((Matrix.reindex e finSumFinEquiv M)ᴴ * (Matrix.reindex e finSumFinEquiv M))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂))) := by
    rw [hgr, ringInverse_reindexB, ringInverse_fromBlocks_diag _ _ h₁ h₂]
  unfold orthProj
  rw [hinv, Matrix.conjTranspose_reindex]
  rw [← reindex_mul_rectB M
        (Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂)))
        e finSumFinEquiv finSumFinEquiv]
  rw [← reindex_mul_rectB
        (M * Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂)))
        Mᴴ e finSumFinEquiv e]
  congr 1
  rw [hM, hconj, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The `recipB` of a block-diagonal matrix is the block-diagonal of the `recipB`s, up to the
index shuffle `blkEquiv n k` / `finSumFinEquiv`. -/
private theorem recipB_blockB {R : Type} [Ring R] {n k : ℕ}
    (G₁ : Matrix (Fin n) (Fin n) R) (G₂ : Matrix (Fin k) (Fin k) R) :
    recipB R (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂))
      = Matrix.reindex (blkEquiv n k) finSumFinEquiv
          (Matrix.fromBlocks (recipB R G₁) 0 0 (recipB R G₂)) := by
  apply (Matrix.reindex (blkEquiv n k) finSumFinEquiv).symm.injective
  rw [Equiv.symm_apply_apply, Matrix.reindex_symm]
  ext i j
  have hcast : ∀ (b : Fin n) (j : Fin k), ¬ (Fin.castAdd k b = Fin.natAdd n j) := by
    intro b j h
    have h1 : (Fin.castAdd k b).val = (Fin.natAdd n j).val := by rw [h]
    have h2 : (Fin.castAdd k b).val < n := Fin.castAdd_lt k b
    have h3 : n ≤ (Fin.natAdd n j).val := by simp [Fin.natAdd]
    omega
  have hnat : ∀ (j : Fin n) (d : Fin k), ¬ (Fin.natAdd n d = Fin.castAdd k j) := by
    intro j d h
    have h1 : (Fin.natAdd n d).val = (Fin.castAdd k j).val := by rw [h]
    have h2 : (Fin.castAdd k j).val < n := Fin.castAdd_lt k j
    have h3 : n ≤ (Fin.natAdd n d).val := by simp [Fin.natAdd]
    omega
  rcases i with ((a | b) | (c | d)) <;> rcases j with (j' | j'') <;>
    simp [Matrix.reindex_apply, recipB, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hcast, hnat]

theorem recipProj_blockB {Y : Type} [TopologicalSpace Y] (n k : ℕ)
    (G₁ : Matrix (Fin n) (Fin n) C(Y, ℂ))
    (G₂ : Matrix (Fin k) (Fin k) C(Y, ℂ)) :
    Work.KT.Fund.recipProj C(Y, ℂ)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks G₁ 0 0 G₂))
      = Matrix.reindex (Work.KT.Fund.blkEquiv n k) (Work.KT.Fund.blkEquiv n k)
          (Matrix.fromBlocks (Work.KT.Fund.recipProj C(Y, ℂ) G₁) 0 0
            (Work.KT.Fund.recipProj C(Y, ℂ) G₂)) := by
  have h₁ : IsUnit ((recipB C(Y, ℂ) G₁)ᴴ * recipB C(Y, ℂ) G₁) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) G₁ G₁).2]
    exact isUnit_one_add_conjTranspose_mul G₁
  have h₂ : IsUnit ((recipB C(Y, ℂ) G₂)ᴴ * recipB C(Y, ℂ) G₂) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) G₂ G₂).2]
    exact isUnit_one_add_conjTranspose_mul G₂
  unfold recipProj
  rw [recipB_blockB]
  exact orthProj_reindex_blkB (recipB C(Y, ℂ) G₁) (recipB C(Y, ℂ) G₂) h₁ h₂

end Work.KT.Fund
