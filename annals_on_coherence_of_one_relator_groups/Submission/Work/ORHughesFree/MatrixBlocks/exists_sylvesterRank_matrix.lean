/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Sylvester rank function induced on a matrix ring

Given a Sylvester matrix rank function `rk` on a ring `U` and a positive integer `n`, the
assignment
`A ↦ rk (flattenBlocks A) / n`
on `k × l` matrices of `n × n` blocks over `U` is a Sylvester rank function on the matrix ring
`Mat_n(U)`, and it is faithful whenever `rk` is ([JZLA20, §2.4], proof of Lemma 2.7).  The main
point is that `flattenBlocks` turns the block constructions `blockDiagFin` and `blockUpperFin`
into the corresponding constructions on flattened matrices, up to the raw identification
`k * n + p * n = (k + p) * n` of the index sets.

The file records the index bookkeeping (`sigmaEquiv`, `tauEquiv` and the comparison
`tauEquiv_eq_finCongr`) and the resulting commutation lemmas
`flattenBlocks_blockDiagFin`, `blockUpperFin_flattenBlocks`, `flattenBlocks_oneByOne`.
-/
import Mathlib
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.Faithful.isFaithful_iff
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul

set_option autoImplicit false

namespace Work.ORHughesFree.MatrixBlocks

open Matrix

/-! ## Index conventions for flattened block matrices

`flattenBlocks` uses the row-major identification `Fin k × Fin n ≃ Fin (k*n)`.  Decomposing the
`k+p` block rows as `Fin k ⊕ Fin p` therefore identifies the rows of a flattened block-diagonal
or block-upper-triangular matrix with `(Fin k ⊕ Fin p) × Fin n`.  There are two natural ways of
naming that set inside a `Fin`: `sigmaEquiv` uses the block order `Fin ((k+p)*n)`, while
`tauEquiv` uses the order `Fin (k*n + p*n)` of the flattened pieces. -/

/-- Rows of a `k+p` block matrix, read through the block order `Fin ((k+p)*n)`. -/
def sigmaEquiv (k p n : ℕ) : (Fin k ⊕ Fin p) × Fin n ≃ Fin ((k + p) * n) :=
  (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin n))).trans finProdFinEquiv

/-- Rows of a `k+p` block matrix, read through the block order `Fin (k*n + p*n)`. -/
def tauEquiv (k p n : ℕ) : (Fin k ⊕ Fin p) × Fin n ≃ Fin (k * n + p * n) :=
  (Equiv.sumProdDistrib (Fin k) (Fin p) (Fin n)).trans
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)

@[simp]
theorem sigmaEquiv_apply {k p n : ℕ} (x : (Fin k ⊕ Fin p) × Fin n) :
    sigmaEquiv k p n x = finProdFinEquiv (finSumFinEquiv x.1, x.2) := rfl

@[simp]
theorem tauEquiv_apply {k p n : ℕ} (x : (Fin k ⊕ Fin p) × Fin n) :
    tauEquiv k p n x = finSumFinEquiv ((Equiv.sumProdDistrib (Fin k) (Fin p) (Fin n) x).map
      (fun z : Fin k × Fin n => finProdFinEquiv z)
      (fun z : Fin p × Fin n => finProdFinEquiv z)) := rfl

/-- The two ways of reading the rows of a `k+p` block matrix differ by the raw identification
`k * n + p * n = (k + p) * n` of index sets: both count the entry `(i, a)` of the block index
`i : Fin k ⊕ Fin p` and the inner index `a : Fin n` by the same natural number. -/
theorem tauEquiv_eq_finCongr {k p n : ℕ} (x : (Fin k ⊕ Fin p) × Fin n) :
    tauEquiv k p n x = finCongr (Nat.add_mul k p n) (sigmaEquiv k p n x) := by
  obtain ⟨s, a⟩ := x
  rcases s with i | i <;>
    simp [tauEquiv, sigmaEquiv, finCongr_apply, Equiv.prodCongr_apply,
      Equiv.sumProdDistrib_apply_left, Equiv.sumProdDistrib_apply_right, Equiv.sumCongr_apply,
      Fin.ext_iff]
  all_goals ring

/-- If two matrices agree after being reparametrised by `sigmaEquiv` and by `tauEquiv`
respectively, then they differ by the raw identification of the index sets. -/
theorem eq_reindex_of_submatrix {R : Type*} [Ring R] {n k l p q : ℕ}
    {X : Matrix (Fin ((k + p) * n)) (Fin ((l + q) * n)) R}
    {W : Matrix (Fin (k * n + p * n)) (Fin (l * n + q * n)) R}
    (h : X.submatrix (⇑(sigmaEquiv k p n)) (⇑(sigmaEquiv l q n))
        = W.submatrix (⇑(tauEquiv k p n)) (⇑(tauEquiv l q n))) :
    X = Matrix.reindex ((finCongr (Nat.add_mul k p n)).symm)
      ((finCongr (Nat.add_mul l q n)).symm) W := by
  have h2 : W.submatrix (⇑(tauEquiv k p n)) (⇑(tauEquiv l q n))
      = (W.submatrix (⇑(finCongr (Nat.add_mul k p n)))
          (⇑(finCongr (Nat.add_mul l q n)))).submatrix
          (⇑(sigmaEquiv k p n)) (⇑(sigmaEquiv l q n)) := by
    rw [Matrix.submatrix_submatrix]
    congr 1
    · exact funext fun x => tauEquiv_eq_finCongr x
    · exact funext fun x => tauEquiv_eq_finCongr x
  have h3 : X.submatrix (⇑(sigmaEquiv k p n)) (⇑(sigmaEquiv l q n))
      = (W.submatrix (⇑(finCongr (Nat.add_mul k p n)))
          (⇑(finCongr (Nat.add_mul l q n)))).submatrix
          (⇑(sigmaEquiv k p n)) (⇑(sigmaEquiv l q n)) := by
    rw [h, h2]
  have h4 := congrArg (fun M : Matrix ((Fin k ⊕ Fin p) × Fin n) ((Fin l ⊕ Fin q) × Fin n) R =>
      M.submatrix (⇑(sigmaEquiv k p n).symm) (⇑(sigmaEquiv l q n).symm)) h3
  simp only [Matrix.submatrix_submatrix, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id, Matrix.submatrix_id_id] at h4
  rw [Matrix.reindex_apply]
  exact h4

/-! ## Flattening the block constructions -/

/-- Flattening commutes with the block diagonal construction, up to the raw identification of
the index sets. -/
theorem flattenBlocks_blockDiagFin {R : Type*} [Ring R] (n k l p q : ℕ)
    (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) R))
    (B : Matrix (Fin p) (Fin q) (Matrix (Fin n) (Fin n) R)) :
    flattenBlocks (blockDiagFin A B) =
      Matrix.reindex ((finCongr (Nat.add_mul k p n)).symm) ((finCongr (Nat.add_mul l q n)).symm)
        (blockDiagFin (flattenBlocks A) (flattenBlocks B)) :=
  eq_reindex_of_submatrix (by
    ext x y
    obtain ⟨s, a⟩ := x
    obtain ⟨t, b⟩ := y
    rcases s with i | i <;> rcases t with j | j <;>
      simp [flattenBlocks, blockDiagFin, Matrix.submatrix_apply, sigmaEquiv, tauEquiv,
        Equiv.prodCongr_apply])

/-- Flattening commutes with the block upper triangular construction, up to the raw
identification of the index sets. -/
theorem blockUpperFin_flattenBlocks {R : Type*} [Ring R] (n k l p q : ℕ)
    (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) R))
    (B : Matrix (Fin p) (Fin q) (Matrix (Fin n) (Fin n) R))
    (C : Matrix (Fin k) (Fin q) (Matrix (Fin n) (Fin n) R)) :
    flattenBlocks (blockUpperFin A B C) =
      Matrix.reindex ((finCongr (Nat.add_mul k p n)).symm) ((finCongr (Nat.add_mul l q n)).symm)
        (blockUpperFin (flattenBlocks A) (flattenBlocks B) (flattenBlocks C)) :=
  eq_reindex_of_submatrix (by
    ext x y
    obtain ⟨s, a⟩ := x
    obtain ⟨t, b⟩ := y
    rcases s with i | i <;> rcases t with j | j <;>
      simp [flattenBlocks, blockUpperFin, Matrix.submatrix_apply, sigmaEquiv, tauEquiv,
        Equiv.prodCongr_apply])

/-- Flattening a `1 × 1` matrix of blocks is the raw identification of the index sets. -/
theorem flattenBlocks_oneByOne {R : Type*} [Ring R] (n : ℕ)
    (a : Matrix (Fin n) (Fin n) R) :
    flattenBlocks (oneByOne a) =
      Matrix.reindex ((finCongr (Nat.one_mul n)).symm) ((finCongr (Nat.one_mul n)).symm) a := by
  have hkey : ∀ I : Fin (1 * n), Fin.cast (Nat.one_mul n) I = I.modNat := by
    intro I
    apply Fin.ext
    show (I.val : ℕ) = I.val % n
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_eq I.isLt (Nat.one_mul n))]
  ext I J
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, flattenBlocks, oneByOne,
    finProdFinEquiv_symm_apply, finCongr_apply, Equiv.symm_symm]
  rw [hkey I, hkey J]

/-! ## The induced rank function on the matrix ring -/

theorem exists_sylvesterRank_matrix {U : Type*} [Ring U] (rk : SylvesterRank U)
    (hfaith : rk.IsFaithful) (n : ℕ) (hn : 0 < n) :
    ∃ rkN : SylvesterRank (Matrix (Fin n) (Fin n) U),
      rkN.IsFaithful ∧
      ∀ (k l : ℕ) (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) U)),
        rkN.rk k l A = rk.rk (k * n) (l * n) (flattenBlocks A) / n := by
  refine ⟨{ rk := fun k l A => rk.rk (k * n) (l * n) (flattenBlocks A) / (n : ℝ),
            rk_nonneg := ?_,
            rk_zero := ?_,
            rk_one := ?_,
            rk_mul_le_left := ?_,
            rk_mul_le_right := ?_,
            rk_blockDiag := ?_,
            rk_blockUpper := ?_ }, ?_, ?_⟩
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
  · intro a ha
    have h1 : rk.rk (1 * n) (1 * n) (flattenBlocks (oneByOne a)) / (n : ℝ) = 0 := ha
    rw [flattenBlocks_oneByOne, RankAPI.rk_reindex rk ((finCongr (Nat.one_mul n)).symm)
      ((finCongr (Nat.one_mul n)).symm) a] at h1
    have h2 : rk.rk n n a = 0 := by
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact h
      · exact absurd h (by positivity)
    by_contra hne
    exact (Faithful.isFaithful_iff rk).mp hfaith n n a hne h2
  · intro k l A
    rfl

end Work.ORHughesFree.MatrixBlocks
