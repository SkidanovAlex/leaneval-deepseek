/-
Generated universe-`u` copies of the universe-0 lemmas needed for the
universe-polymorphic natural extension theorem.
-/

import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.RankAPI.rk_reindex

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORHughesFree.NaturalExtensionGen.BlockDiag

open Matrix
open Work.ORHughesFree.NaturalExtension

/- copy of NaturalExtension/rk_trunc_blockDiagFin2.lean -/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The truncation of a block diagonal matrix

For a matrix `A` over `U[t^{±1};τ]`, the truncation `trunc i A` (see `Defs.lean`) is the matrix
over `U` of "right multiplication by `A`" on the truncated module
`(U[t;τ]/t^iU[t;τ])ⁿ`, expressed in the basis `{t^r e_p}`.

The main result of this file is that the truncation of a block diagonal matrix is, up to a
suitable identification of the index sets, the block diagonal of the truncations:

`rk ((n+p)i) ((m+q)i) (trunc i (blockDiagFin A B)) = rk (ni) (mi) (trunc i A) +
rk (pi) (qi) (trunc i B)`.

This is the exact analogue of the Sylvester rank axiom (SMat3) for the truncation: the truncation
functor is additive on block diagonal matrices.  The proof is purely combinatorial: on the
diagonal blocks the coefficient matrices of `blockDiagFin A B` agree with those of `A` and `B`
respectively, and off the diagonal they vanish.

## Main results

* `toep_blockDiagFin` : the truncated (block Toeplitz) matrix of a block diagonal matrix agrees
  with the block diagonal of the truncated matrices, up to reindexing.
* `reindex_trunc_blockDiagFin` : the same statement for `trunc`.
* `rk_trunc_blockDiagFin2` : additivity of the truncated rank on block diagonal matrices.
-/



open Matrix

/-! ### The blocks of `blockDiagFin` -/

section Blocks

/-- The inverse of `finSumFinEquiv` on the left block. -/
lemma finSumFinEquiv_symm_castAdd {m n : ℕ} (i : Fin m) :
    (finSumFinEquiv (m := m) (n := n)).symm (Fin.castAdd n i) = Sum.inl i := by
  rw [← finSumFinEquiv_apply_left, Equiv.symm_apply_apply]

/-- The inverse of `finSumFinEquiv` on the right block. -/
lemma finSumFinEquiv_symm_natAdd {m n : ℕ} (j : Fin n) :
    (finSumFinEquiv (m := m) (n := n)).symm (Fin.natAdd m j) = Sum.inr j := by
  rw [← finSumFinEquiv_apply_right, Equiv.symm_apply_apply]

/-- The top left block of `blockDiagFin A B` is `A`. -/
lemma blockDiagFin_apply_castAdd_castAdd {R : Type*} [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin n) (j : Fin m) :
    blockDiagFin A B (Fin.castAdd p i) (Fin.castAdd q j) = A i j := by
  rw [blockDiagFin, Matrix.submatrix_apply, finSumFinEquiv_symm_castAdd,
    finSumFinEquiv_symm_castAdd, Matrix.fromBlocks_apply₁₁]

/-- The top right block of `blockDiagFin A B` vanishes. -/
lemma blockDiagFin_apply_castAdd_natAdd {R : Type*} [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin n) (j : Fin q) :
    blockDiagFin A B (Fin.castAdd p i) (Fin.natAdd m j) = 0 := by
  rw [blockDiagFin, Matrix.submatrix_apply, finSumFinEquiv_symm_castAdd,
    finSumFinEquiv_symm_natAdd, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

/-- The bottom left block of `blockDiagFin A B` vanishes. -/
lemma blockDiagFin_apply_natAdd_castAdd {R : Type*} [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin p) (j : Fin m) :
    blockDiagFin A B (Fin.natAdd n i) (Fin.castAdd q j) = 0 := by
  rw [blockDiagFin, Matrix.submatrix_apply, finSumFinEquiv_symm_natAdd,
    finSumFinEquiv_symm_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The bottom right block of `blockDiagFin A B` is `B`. -/
lemma blockDiagFin_apply_natAdd_natAdd {R : Type*} [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) (i : Fin p) (j : Fin q) :
    blockDiagFin A B (Fin.natAdd n i) (Fin.natAdd m j) = B i j := by
  rw [blockDiagFin, Matrix.submatrix_apply, finSumFinEquiv_symm_natAdd,
    finSumFinEquiv_symm_natAdd, Matrix.fromBlocks_apply₂₂]

/-- Coefficient extraction commutes with the block diagonal construction. -/
lemma coeffMat_blockDiagFin {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin p) (Fin q) (SkewL U)) (k : ℤ) :
    coeffMat (blockDiagFin A B) k = blockDiagFin (coeffMat A k) (coeffMat B k) := by
  have h0 : coeffElt (0 : SkewL U) k = 0 := by
    simp [coeffElt, SkewMonoidAlgebra.coeff_zero]
  simp only [coeffMat, blockDiagFin]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  rw [Matrix.map_zero (f := fun a => coeffElt a k) h0,
      Matrix.map_zero (f := fun a => coeffElt a k) h0]

end Blocks

/-! ### Reindexing the truncation of a block diagonal matrix

The index set of `toep i A` is the product `Fin n × Fin i` of the "block" index and the
"coefficient degree" index.  On a block diagonal matrix the block index splits as
`Fin n ⊕ Fin p`, and this is exactly what the auxiliary equivalences below express. -/

section Reindex

/-- The row reindexing taking the (split) block index of `blockDiagFin A B` to the block index of
`fromBlocks (toep i A) 0 0 (toep i B)`. -/
noncomputable def blockDiagRowEquiv (n p i : ℕ) :
    (Fin n × Fin i) ⊕ (Fin p × Fin i) ≃ Fin (n + p) × Fin i :=
  (Equiv.sumProdDistrib (Fin n) (Fin p) (Fin i)).symm.trans
    ((finSumFinEquiv (m := n) (n := p)).prodCongr (Equiv.refl (Fin i)))

lemma blockDiagRowEquiv_symm_castAdd {n p i : ℕ} (a : Fin n) (r : Fin i) :
    (blockDiagRowEquiv n p i).symm (Fin.castAdd p a, r) = Sum.inl (a, r) := by
  simp [blockDiagRowEquiv, Equiv.prodCongr_apply, Equiv.sumProdDistrib]

lemma blockDiagRowEquiv_symm_natAdd {n p i : ℕ} (a : Fin p) (r : Fin i) :
    (blockDiagRowEquiv n p i).symm (Fin.natAdd n a, r) = Sum.inr (a, r) := by
  simp [blockDiagRowEquiv, Equiv.prodCongr_apply, Equiv.sumProdDistrib]

/-- The truncation of a block diagonal matrix is the block diagonal of the truncations, up to
reindexing: the entry at `((q,r),(s,p))` in the diagonal blocks is the corresponding entry of the
truncation of `A` or `B`, and the off-diagonal blocks of the truncation vanish. -/
theorem toep_blockDiagFin {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m p q : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin p) (Fin q) (SkewL U)) :
    toep i (blockDiagFin A B) =
      Matrix.reindex (blockDiagRowEquiv n p i) (blockDiagRowEquiv m q i)
        (Matrix.fromBlocks (toep i A) 0 0 (toep i B)) := by
  ext x y
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  obtain ⟨x', rfl⟩ := (finSumFinEquiv (m := n) (n := p)).surjective x1
  obtain ⟨y', rfl⟩ := (finSumFinEquiv (m := m) (n := q)).surjective y1
  rcases x' with a | a <;> rcases y' with c | c
  all_goals
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  · simp only [toep, Matrix.reindex_apply, Matrix.submatrix_apply, blockDiagRowEquiv_symm_castAdd,
      Matrix.fromBlocks_apply₁₁, coeffMat_blockDiagFin, Matrix.smul_apply,
      blockDiagFin_apply_castAdd_castAdd]
  · simp only [toep, Matrix.reindex_apply, Matrix.submatrix_apply, blockDiagRowEquiv_symm_castAdd,
      blockDiagRowEquiv_symm_natAdd, Matrix.fromBlocks_apply₁₂, coeffMat_blockDiagFin,
      Matrix.smul_apply, blockDiagFin_apply_castAdd_natAdd, smul_zero, Matrix.zero_apply]
  · simp only [toep, Matrix.reindex_apply, Matrix.submatrix_apply, blockDiagRowEquiv_symm_natAdd,
      blockDiagRowEquiv_symm_castAdd, Matrix.fromBlocks_apply₂₁, coeffMat_blockDiagFin,
      Matrix.smul_apply, blockDiagFin_apply_natAdd_castAdd, smul_zero, Matrix.zero_apply]
  · simp only [toep, Matrix.reindex_apply, Matrix.submatrix_apply, blockDiagRowEquiv_symm_natAdd,
      Matrix.fromBlocks_apply₂₂, coeffMat_blockDiagFin, Matrix.smul_apply,
      blockDiagFin_apply_natAdd_natAdd]

/-- The row reindexing taking the index set `Fin ((n+p)*i)` of `trunc i (blockDiagFin A B)` to the
index set `Fin (n*i + p*i)` of `blockDiagFin (trunc i A) (trunc i B)`. -/
noncomputable def truncBlockRowEquiv (n p i : ℕ) : Fin ((n + p) * i) ≃ Fin (n * i + p * i) :=
  ((blockDiagRowEquiv n p i).trans (finProdFinEquiv (m := n + p) (n := i))).symm.trans
    (((finProdFinEquiv (m := n) (n := i)).sumCongr (finProdFinEquiv (m := p) (n := i))).trans
      (finSumFinEquiv (m := n * i) (n := p * i)))

lemma truncBlockRowEquiv_symm_finSumFinEquiv_inl {n p i : ℕ} (a : Fin (n * i)) :
    (truncBlockRowEquiv n p i).symm (finSumFinEquiv (Sum.inl a))
      = finProdFinEquiv (Fin.castAdd p a.divNat, a.modNat) := by
  simp [truncBlockRowEquiv, Equiv.symm_symm, Equiv.sumCongr_apply, blockDiagRowEquiv,
    Equiv.prodCongr_apply, Equiv.sumProdDistrib, finProdFinEquiv_symm_apply]

lemma truncBlockRowEquiv_symm_castAdd {n p i : ℕ} (a : Fin (n * i)) :
    (truncBlockRowEquiv n p i).symm (Fin.castAdd (p * i) a)
      = finProdFinEquiv (Fin.castAdd p a.divNat, a.modNat) := by
  rw [show Fin.castAdd (p * i) a = finSumFinEquiv (Sum.inl a) from
    (finSumFinEquiv_apply_left (m := n * i) (n := p * i) a).symm]
  exact truncBlockRowEquiv_symm_finSumFinEquiv_inl a

lemma truncBlockRowEquiv_symm_natAdd {n p i : ℕ} (b : Fin (p * i)) :
    (truncBlockRowEquiv n p i).symm (Fin.natAdd (n * i) b)
      = finProdFinEquiv (Fin.natAdd n b.divNat, b.modNat) := by
  rw [show Fin.natAdd (n * i) b = finSumFinEquiv (Sum.inr b) from
    (finSumFinEquiv_apply_right (m := n * i) (n := p * i) b).symm]
  simp [truncBlockRowEquiv, Equiv.symm_symm, Equiv.sumCongr_apply, blockDiagRowEquiv,
    Equiv.prodCongr_apply, Equiv.sumProdDistrib, finProdFinEquiv_symm_apply]

/-- The truncation of a block diagonal matrix is the block diagonal of the truncations, up to
reindexing. -/
theorem reindex_trunc_blockDiagFin {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m p q : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin p) (Fin q) (SkewL U)) :
    Matrix.reindex (truncBlockRowEquiv n p i) (truncBlockRowEquiv m q i)
        (trunc i (blockDiagFin A B))
      = blockDiagFin (trunc i A) (trunc i B) := by
  ext x y
  obtain ⟨x', rfl⟩ := (finSumFinEquiv (m := n * i) (n := p * i)).surjective x
  obtain ⟨y', rfl⟩ := (finSumFinEquiv (m := m * i) (n := q * i)).surjective y
  rcases x' with a | a <;> rcases y' with c | c <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      truncBlockRowEquiv_symm_castAdd, truncBlockRowEquiv_symm_natAdd, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, blockDiagFin_apply_castAdd_castAdd,
      blockDiagFin_apply_castAdd_natAdd, blockDiagFin_apply_natAdd_castAdd,
      blockDiagFin_apply_natAdd_natAdd, coeffMat_blockDiagFin, Matrix.smul_apply, smul_zero,
      Matrix.zero_apply, trunc_apply, MatrixBlocks.finProdFinEquiv_fst,
      MatrixBlocks.finProdFinEquiv_snd]

end Reindex

/-- The truncation functor is additive on block diagonal matrices: the rank of the truncation of
`blockDiagFin A B` is the sum of the ranks of the truncations of `A` and of `B`.

This is the truncated form of the Sylvester rank axiom (SMat3), and the input to the natural
extension construction. -/
theorem rk_trunc_blockDiagFin2 {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) {n m p q : ℕ} (i : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin p) (Fin q) (SkewL U)) :
    rk.rk ((n + p) * i) ((m + q) * i) (trunc i (blockDiagFin A B)) =
      rk.rk (n * i) (m * i) (trunc i A) + rk.rk (p * i) (q * i) (trunc i B) := by
  rw [← RankAPI.rk_reindex rk (truncBlockRowEquiv n p i) (truncBlockRowEquiv m q i)
      (trunc i (blockDiagFin A B))]
  rw [reindex_trunc_blockDiagFin, rk.rk_blockDiag]

end Work.ORHughesFree.NaturalExtensionGen.BlockDiag
