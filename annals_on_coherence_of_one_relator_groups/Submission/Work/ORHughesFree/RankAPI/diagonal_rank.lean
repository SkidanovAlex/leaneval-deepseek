/-
# The rank of a diagonal matrix

This file proves that a Sylvester matrix rank function is additive on diagonal matrices:

  `rk (diagonal a) = ∑ j, rk (oneByOne (a j))`.

The proof is an induction on the size `k`, using the fact (established here as
`diagonal_eq_blockDiagFin`) that the `(k+1) × (k+1)` diagonal matrix with entries `a`
is, under the standard identification `Fin k ⊕ Fin 1 ≃ Fin (k+1)`, the block diagonal
matrix of the `k × k` diagonal matrix with entries `a ∘ Fin.castSucc` and the `1 × 1`
matrix `oneByOne (a (Fin.last k))`, together with the block-diagonal axiom `(SMat3)`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false

namespace Work.ORHughesFree.RankAPI

open Matrix Work.ORHughesFree

/-- The last index of `Fin (k + 1)` written as `Fin.natAdd k u` for the unique `u : Fin 1`. -/
lemma fin_natAdd_eq_last (k : ℕ) (u : Fin 1) : (Fin.natAdd k u : Fin (k + 1)) = Fin.last k := by
  ext; simp

/-- The diagonal matrix of size `k + 1` splits, under the equivalence
`Fin k ⊕ Fin 1 ≃ Fin (k + 1)`, into the block diagonal of the diagonal matrix of size `k`
with entries `a ∘ Fin.castSucc` and the `1 × 1` matrix with entry `a (Fin.last k)`. -/
lemma diagonal_eq_blockDiagFin {R : Type*} [Ring R] {k : ℕ} (a : Fin (k + 1) → R) :
    Matrix.diagonal a
      = blockDiagFin (Matrix.diagonal (fun i : Fin k => a i.castSucc))
          (oneByOne (a (Fin.last k))) := by
  have h1 : Matrix.diagonal a
      = (Matrix.diagonal (fun u : Fin k ⊕ Fin 1 => a (finSumFinEquiv u))).submatrix
          (⇑(finSumFinEquiv (m := k) (n := 1)).symm) (⇑finSumFinEquiv.symm) := by
    rw [Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    simp
  have h2 : Matrix.diagonal (fun u : Fin k ⊕ Fin 1 => a (finSumFinEquiv u))
      = Matrix.fromBlocks (Matrix.diagonal (fun i : Fin k => a i.castSucc)) 0
          (0 : Matrix (Fin 1) (Fin k) R) (oneByOne (a (Fin.last k))) := by
    ext u v
    rcases u with i | i <;> rcases v with j | j
    · simp only [Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left,
        Sum.inl.injEq]
      rfl
    · simp [Matrix.fromBlocks_apply₁₂]
    · simp [Matrix.fromBlocks_apply₂₁]
    · rw [Subsingleton.elim i j]
      simp [Matrix.fromBlocks_apply₂₂, oneByOne, finSumFinEquiv_apply_right, fin_natAdd_eq_last]
  rw [h1, h2, blockDiagFin]

/-- A Sylvester matrix rank function is additive on diagonal matrices: the rank of the
diagonal matrix with entries `a j` is the sum of the ranks of the `1 × 1` matrices with
entries `a j`. -/
theorem diagonal_rank {R : Type*} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R) {k : ℕ}
    (a : Fin k → R) :
    rk.rk k k (Matrix.diagonal a)
      = ∑ j : Fin k, rk.rk 1 1 (Work.ORHughesFree.oneByOne (a j)) := by
  induction k with
  | zero =>
    have h : (Matrix.diagonal a : Matrix (Fin 0) (Fin 0) R) = 0 := by
      ext i
      exact Fin.elim0 i
    rw [h, rk.rk_zero]
    simp
  | succ k ih =>
    rw [diagonal_eq_blockDiagFin a, rk.rk_blockDiag]
    rw [ih (fun i : Fin k => a i.castSucc)]
    rw [Fin.sum_univ_castSucc]

end Work.ORHughesFree.RankAPI
