import Mathlib
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.kappa_add_defs
import Submission.Work.KT.Fund.graphProj_block_defs
import Submission.Work.KT.Fund.graphProj_block_aux
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul

/-!
# `Work.KT.Fund.graphProj_blockB` — block decomposition of `graphProj`

`graphProj R F = orthProj R (graphB R F)` is the orthogonal projection onto the graph of `F`.
The orthogonal projection of a *block-diagonal* matrix splits as the block diagonal of the
orthogonal projections of the blocks.  Concretely, for `F = F₁ ⊕ F₂` (viewed as a matrix on
`Fin (n + k)` via `finSumFinEquiv`),

`graphProj C(Y,ℂ) (reindex finSumFinEquiv finSumFinEquiv (fromBlocks F₁ 0 0 F₂))`

is `reindex (blkEquiv n k) (blkEquiv n k)` of the block-diagonal matrix with blocks
`graphProj C(Y,ℂ) F₁` and `graphProj C(Y,ℂ) F₂`.

The proof is entirely algebraic and mirrors the `recipProj` case.  Writing `Bᵢ = graphB R Fᵢ`
and `f = finSumFinEquiv`, `e = blkEquiv n k`, one has

* `graphB R (reindex f f (fromBlocks F₁ 0 0 F₂)) = reindex e f (fromBlocks B₁ 0 0 B₂)`
  (a purely combinatorial identity of index types);
* `orthProj R` of a matrix of the form `reindex e f (fromBlocks B₁ 0 0 B₂)` splits, because
  `conjTranspose`, multiplication and `Ring.inverse` all respect the reindexing equivalences and
  the inverse of a block-diagonal matrix is block-diagonal.
-/

namespace Work.KT.Fund

open scoped Matrix
open _root_.Matrix

noncomputable section

/-- Reindexing a product of rectangular matrices. -/
private theorem reindex_mul_rect_aux {α : Type} [AddCommMonoid α] [Mul α]
    {l m n o p q : Type} [Fintype m] [Fintype n] [Fintype o]
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : m ≃ l) (e₂ : n ≃ o) (e₃ : p ≃ q) :
    Matrix.reindex e₁ e₃ (M * N) = Matrix.reindex e₁ e₂ M * Matrix.reindex e₂ e₃ N := by
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv M N e₁.symm e₂.symm e₃.symm]

/-- `orthProj` of a matrix which is a block diagonal in the `Fin n` and `Fin k` blocks (viewed
through `blkEquiv n k` and `finSumFinEquiv`) is the block diagonal of the `orthProj`s of the
blocks. -/
private theorem orthProj_reindex_blk_aux {R : Type} [CommRing R] [StarRing R] {n k : ℕ}
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
      ← reindex_mul_rect_aux Mᴴ M finSumFinEquiv e finSumFinEquiv, hMM]
  have hinv : Ring.inverse
        ((Matrix.reindex e finSumFinEquiv M)ᴴ * (Matrix.reindex e finSumFinEquiv M))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂))) := by
    rw [hgr, Matrix.ringInverse_reindex, ringInverse_fromBlocks_diag _ _ h₁ h₂]
  unfold orthProj
  rw [hinv, Matrix.conjTranspose_reindex]
  rw [← reindex_mul_rect_aux M
        (Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂)))
        e finSumFinEquiv finSumFinEquiv]
  rw [← reindex_mul_rect_aux
        (M * Matrix.fromBlocks (Ring.inverse (B₁ᴴ * B₁)) 0 0 (Ring.inverse (B₂ᴴ * B₂)))
        Mᴴ e finSumFinEquiv e]
  congr 1
  rw [hM, hconj, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The `graphB` of a block-diagonal matrix is the block-diagonal of the `graphB`s, up to the
index shuffle `blkEquiv n k` / `finSumFinEquiv`. -/
private theorem graphB_reindex_block {R : Type} [Ring R] {n k : ℕ}
    (F₁ : Matrix (Fin n) (Fin n) R) (F₂ : Matrix (Fin k) (Fin k) R) :
    graphB R (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
      = Matrix.reindex (blkEquiv n k) finSumFinEquiv
          (Matrix.fromBlocks (graphB R F₁) 0 0 (graphB R F₂)) := by
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
    simp [Matrix.reindex_apply, graphB, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, hcast, hnat]

theorem graphProj_blockB {Y : Type} [TopologicalSpace Y] (n k : ℕ)
    (F₁ : Matrix (Fin n) (Fin n) C(Y, ℂ))
    (F₂ : Matrix (Fin k) (Fin k) C(Y, ℂ)) :
    Work.KT.Fund.graphProj C(Y, ℂ)
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F₁ 0 0 F₂))
      = Matrix.reindex (Work.KT.Fund.blkEquiv n k) (Work.KT.Fund.blkEquiv n k)
          (Matrix.fromBlocks (Work.KT.Fund.graphProj C(Y, ℂ) F₁) 0 0
            (Work.KT.Fund.graphProj C(Y, ℂ) F₂)) := by
  have h₁ : IsUnit ((graphB C(Y, ℂ) F₁)ᴴ * graphB C(Y, ℂ) F₁) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) F₁ F₁).1]
    exact isUnit_one_add_conjTranspose_mul F₁
  have h₂ : IsUnit ((graphB C(Y, ℂ) F₂)ᴴ * graphB C(Y, ℂ) F₂) := by
    rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) F₂ F₂).1]
    exact isUnit_one_add_conjTranspose_mul F₂
  unfold graphProj
  rw [graphB_reindex_block]
  exact orthProj_reindex_blk_aux (graphB C(Y, ℂ) F₁) (graphB C(Y, ℂ) F₂) h₁ h₂

end

end Work.KT.Fund
