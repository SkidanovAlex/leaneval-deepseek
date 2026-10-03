/-
Generated universe-`u` copies of the universe-0 lemmas needed for the
universe-polymorphic natural extension theorem.
-/

import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.RankAPI.rk_reindex

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORHughesFree.NaturalExtensionGen.BlockUpper

open Matrix
open Work.ORHughesFree.NaturalExtension

/- copy of NaturalExtension/rk_trunc_blockUpperFin2.lean -/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The truncation of a block upper triangular matrix

The truncation construction `trunc i` of `NaturalExtension.Defs` (the "block Toeplitz"
matrix of right multiplication by `A` on `(U[t^{\pm 1};\tau]/t^i)^{\oplus n}`) is compatible
with the block constructions: the truncation of a block upper triangular matrix is, up to the
identification `Fin ((n+p)*i) ≃ Fin (n*i + p*i)` of the row index sets (and the corresponding one
for the columns), the block upper triangular matrix of the truncations.  Consequently the truncated
rank function inherits the axiom (SMat4) of Sylvester rank functions:

`rk (trunc i A) + rk (trunc i B) ≤ rk (trunc i (blockUpperFin A B C))`.

This is the inequality half of the statement that the assignment
`A ↦ rk (trunc i A)` is again a Sylvester matrix rank function on `U`, and it is the input needed
in the construction of the natural extension of `rk` to `U[t^{\pm 1};\tau]`.

## Main results

* `blkIndex` : the block-flattening map `(Fin n ⊕ Fin p) → Fin i → Fin (n*i + p*i)`;
* `trunc_blockUpperFin_apply` : the pointwise computation of `trunc i (blockUpperFin A B C)`;
* `reindex_trunc_blockUpperFin` : `trunc i (blockUpperFin A B C)`, reindexed, is
  `blockUpperFin (trunc i A) (trunc i B) (trunc i C)`;
* `rk_trunc_blockUpperFin2` : the resulting inequality for the rank.
-/


open Matrix

/-- The block-flattening of an index: `(Fin n ⊕ Fin p) × Fin i → Fin (n*i + p*i)`, sending
`(inl a, r)` to the `r`-th inner index of the `a`-th `A`-row, and `(inr b, r)` to the `r`-th
inner index of the `b`-th `B`-row. -/
def blkIndex (n p i : ℕ) : (Fin n ⊕ Fin p) → Fin i → Fin (n * i + p * i)
  | Sum.inl a, r => finSumFinEquiv (Sum.inl (finProdFinEquiv (a, r)))
  | Sum.inr b, r => finSumFinEquiv (Sum.inr (finProdFinEquiv (b, r)))

/-- The underlying natural number of `blkIndex n p i z r`. -/
lemma blkIndex_val {n p i : ℕ} (z : Fin n ⊕ Fin p) (r : Fin i) :
    (blkIndex n p i z r).val = r.val + i * (finSumFinEquiv z).val := by
  rcases z with a | b
  · simp [blkIndex, finProdFinEquiv, finSumFinEquiv_apply_left, Fin.val_castAdd]
  · simp [blkIndex, finProdFinEquiv, finSumFinEquiv_apply_right, Fin.val_natAdd]
    ring

/-- `blkIndex` composed with the `divNat`/`modNat` decomposition of the inner index is the
identification `Fin ((n+p)*i) ≃ Fin (n*i + p*i)` of the two index sets. -/
lemma blkIndex_divNat_modNat {n p i : ℕ} (u : Fin ((n + p) * i)) :
    blkIndex n p i (finSumFinEquiv.symm u.divNat) u.modNat = finCongr (Nat.add_mul n p i) u := by
  have hu : finProdFinEquiv (u.divNat, u.modNat) = u := by
    rw [← finProdFinEquiv_symm_apply]
    exact Equiv.apply_symm_apply _ _
  have huv : u.val = u.modNat.val + i * u.divNat.val := by
    rw [← show (finProdFinEquiv (u.divNat, u.modNat)).val = u.val from congrArg Fin.val hu]
    rfl
  apply Fin.ext
  simp only [blkIndex_val, finCongr_apply, Fin.val_cast, Equiv.apply_symm_apply]
  exact huv.symm

/-- Pointwise computation of the truncation of a block upper triangular matrix: the entry of
`trunc i (blockUpperFin A B C)` at the index `(Q, r)` of the block row and `(P, s)` of the block
column is the corresponding entry of the block upper triangular matrix of the truncations, the
blocks being indexed by `blkIndex`. -/
lemma trunc_blockUpperFin_apply {U : Type u} [AddMonoid U] [SMulZeroClass (Multiplicative ℤ) U]
    {n m p q : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin p) (Fin q) (SkewL U)) (C : Matrix (Fin n) (Fin q) (SkewL U))
    (Q : Fin (n + p)) (P : Fin (m + q)) (r s : Fin i) :
    trunc i (blockUpperFin A B C) (finProdFinEquiv (Q, r)) (finProdFinEquiv (P, s)) =
      blockUpperFin (trunc i A) (trunc i B) (trunc i C)
        (blkIndex n p i (finSumFinEquiv.symm Q) r) (blkIndex m q i (finSumFinEquiv.symm P) s) := by
  have hQ : Q = finSumFinEquiv (finSumFinEquiv.symm Q) := (Equiv.apply_symm_apply _ Q).symm
  have hP : P = finSumFinEquiv (finSumFinEquiv.symm P) := (Equiv.apply_symm_apply _ P).symm
  rw [hQ, hP]
  rcases finSumFinEquiv.symm Q with a | b <;> rcases finSumFinEquiv.symm P with c | d <;>
    simp only [trunc_apply', Matrix.smul_apply, blkIndex, blockUpperFin, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, coeffMat_apply, coeffElt,
      SkewMonoidAlgebra.coeff_zero, Matrix.zero_apply, Finsupp.zero_apply, smul_zero]

/-- The truncation of a block upper triangular matrix is a block upper triangular matrix of the
truncations, up to the identification of the index sets. -/
theorem reindex_trunc_blockUpperFin {U : Type u} [AddMonoid U] [SMulZeroClass (Multiplicative ℤ) U]
    {n m p q : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin p) (Fin q) (SkewL U)) (C : Matrix (Fin n) (Fin q) (SkewL U)) :
    Matrix.reindex (finCongr (Nat.add_mul n p i)) (finCongr (Nat.add_mul m q i))
      (trunc i (blockUpperFin A B C)) = blockUpperFin (trunc i A) (trunc i B) (trunc i C) := by
  ext x y
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  set u : Fin ((n + p) * i) := (finCongr (Nat.add_mul n p i)).symm x with hu
  set v : Fin ((m + q) * i) := (finCongr (Nat.add_mul m q i)).symm y with hv
  have hx : finProdFinEquiv (u.divNat, u.modNat) = u := by
    rw [← finProdFinEquiv_symm_apply]
    exact Equiv.apply_symm_apply _ _
  have hy : finProdFinEquiv (v.divNat, v.modNat) = v := by
    rw [← finProdFinEquiv_symm_apply]
    exact Equiv.apply_symm_apply _ _
  rw [← hx, ← hy, trunc_blockUpperFin_apply, blkIndex_divNat_modNat, blkIndex_divNat_modNat,
    hu, hv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem rk_trunc_blockUpperFin2 {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) {n m p q : ℕ} (i : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin p) (Fin q) (SkewL U))
    (C : Matrix (Fin n) (Fin q) (SkewL U)) :
    rk.rk (n * i) (m * i) (trunc i A) + rk.rk (p * i) (q * i) (trunc i B) ≤
      rk.rk ((n + p) * i) ((m + q) * i) (trunc i (blockUpperFin A B C)) := by
  have key := Work.ORHughesFree.RankAPI.rk_reindex rk (finCongr (Nat.add_mul n p i))
    (finCongr (Nat.add_mul m q i)) (trunc i (blockUpperFin A B C))
  rw [reindex_trunc_blockUpperFin (i := i) (A := A) (B := B) (C := C)] at key
  calc rk.rk (n * i) (m * i) (trunc i A) + rk.rk (p * i) (q * i) (trunc i B)
      ≤ rk.rk (n * i + p * i) (m * i + q * i)
          (blockUpperFin (trunc i A) (trunc i B) (trunc i C)) :=
        rk.rk_blockUpper (trunc i A) (trunc i B) (trunc i C)
    _ = rk.rk ((n + p) * i) ((m + q) * i) (trunc i (blockUpperFin A B C)) := key

end Work.ORHughesFree.NaturalExtensionGen.BlockUpper
