/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Sylvester rank function induced on a matrix ring (unfaithful version)

Given *any* Sylvester matrix rank function `rk` on a ring `U` (no faithfulness hypothesis) and a
positive integer `n`, the assignment
`A ↦ rk (flattenBlocks A) / n`
on `k × l` matrices of `n × n` blocks over `U` is a Sylvester rank function on the matrix ring
`Mat_n(U)` ([JZLA20, §2.4], proof of Lemma 2.7).

This is the same construction as in `exists_sylvesterRank_matrix`, but the faithfulness of `rk`
is neither assumed nor concluded; the rank axioms do not use it.  The index bookkeeping
(`sigmaEquiv`, `tauEquiv`) and the commutation lemmas
`flattenBlocks_blockDiagFin`, `blockUpperFin_flattenBlocks`, `flattenBlocks_oneByOne` come from
that file.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.MatrixBlocks.exists_sylvesterRank_matrix

namespace Work.ORHughesFree.MatrixBlocks

open Matrix

theorem exists_sylvesterRank_matrix_unfaithful {U : Type*} [Ring U] (rk : SylvesterRank U) (n : ℕ) (hn : 0 < n) : ∃ rkN : SylvesterRank (Matrix (Fin n) (Fin n) U), ∀ (k l : ℕ) (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) U)), rkN.rk k l A = rk.rk (k * n) (l * n) (flattenBlocks A) / n := by
  refine ⟨{ rk := fun k l A => rk.rk (k * n) (l * n) (flattenBlocks A) / (n : ℝ),
            rk_nonneg := ?_,
            rk_zero := ?_,
            rk_one := ?_,
            rk_mul_le_left := ?_,
            rk_mul_le_right := ?_,
            rk_blockDiag := ?_,
            rk_blockUpper := ?_ }, ?_⟩
  · intro k l A
    exact div_nonneg (rk.rk_nonneg (k * n) (l * n) _) (Nat.cast_nonneg n)
  · intro k l
    rw [show flattenBlocks (0 : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) U)) = 0 from by
      ext i j
      simp [flattenBlocks]]
    rw [rk.rk_zero, zero_div]
  · rw [show (1 : Matrix (Fin 1) (Fin 1) (Matrix (Fin n) (Fin n) U))
        = oneByOne (1 : Matrix (Fin n) (Fin n) U) from by
      ext i j
      rw [show i = j from Subsingleton.elim i j]
      simp [oneByOne, Matrix.one_apply],
      flattenBlocks_oneByOne]
    rw [RankAPI.rk_reindex rk ((finCongr (Nat.one_mul n)).symm)
        ((finCongr (Nat.one_mul n)).symm) (1 : Matrix (Fin n) (Fin n) U),
      RankAPI.rk_one_fin rk n]
    exact div_self (by exact_mod_cast hn.ne')
  · intro k l m A B
    rw [flattenBlocks_mul]
    exact div_le_div_of_nonneg_right
      (rk.rk_mul_le_left (flattenBlocks A) (flattenBlocks B)) (Nat.cast_nonneg n)
  · intro k l m A B
    rw [flattenBlocks_mul]
    exact div_le_div_of_nonneg_right
      (rk.rk_mul_le_right (flattenBlocks A) (flattenBlocks B)) (Nat.cast_nonneg n)
  · intro k l p q A B
    rw [flattenBlocks_blockDiagFin, RankAPI.rk_reindex rk
        ((finCongr (Nat.add_mul k p n)).symm) ((finCongr (Nat.add_mul l q n)).symm)
        (blockDiagFin (flattenBlocks A) (flattenBlocks B)),
      rk.rk_blockDiag, add_div]
  · intro k l p q A B C
    rw [blockUpperFin_flattenBlocks, RankAPI.rk_reindex rk
        ((finCongr (Nat.add_mul k p n)).symm) ((finCongr (Nat.add_mul l q n)).symm)
        (blockUpperFin (flattenBlocks A) (flattenBlocks B) (flattenBlocks C)), ← add_div]
    exact div_le_div_of_nonneg_right
      (rk.rk_blockUpper (flattenBlocks A) (flattenBlocks B) (flattenBlocks C))
      (Nat.cast_nonneg n)
  · intro k l A
    rfl

end Work.ORHughesFree.MatrixBlocks
