import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix

namespace Work.ORHughesFree.RankAPI

open Work.ORHughesFree

open Matrix

/-- An upper triangular `(n+1) × (n+1)` matrix splits as the block upper triangular matrix with
top-left block the leading `n × n` submatrix, bottom-right block the trailing `1 × 1` submatrix
and bottom-left block `0` (which is exactly the upper triangularity hypothesis). -/
private lemma eq_blockUpperFin_of_upperTriangular {R : Type} [Ring R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i j : Fin (n + 1), (j : ℕ) < (i : ℕ) → M i j = 0) :
    M = blockUpperFin (M.submatrix Fin.castSucc Fin.castSucc)
      (oneByOne (M (Fin.last n) (Fin.last n)))
      (M.submatrix Fin.castSucc (fun _ : Fin 1 => Fin.last n)) := by
  ext i j
  induction i using Fin.addCases with
  | left i' =>
      induction j using Fin.addCases with
      | left j' =>
          simp only [blockUpperFin, Matrix.submatrix_apply,
            finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
          rfl
      | right j' =>
          simp only [blockUpperFin, Matrix.submatrix_apply,
            finSumFinEquiv_symm_apply_castAdd,
            finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₂]
          rw [show Fin.natAdd n j' = Fin.last n from by ext; simp]
          rfl
  | right i' =>
      induction j using Fin.addCases with
      | left j' =>
          simp only [blockUpperFin, Matrix.submatrix_apply,
            finSumFinEquiv_symm_apply_castAdd,
            finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁]
          rw [h (Fin.natAdd n i') (Fin.castAdd 1 j') (by simp)]
          simp
      | right j' =>
          simp only [blockUpperFin, Matrix.submatrix_apply,
            finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
          rw [show Fin.natAdd n i' = Fin.last n from by ext; simp,
              show Fin.natAdd n j' = Fin.last n from by ext; simp]
          rfl

/-- For an upper triangular square matrix (`M i j = 0` whenever `j < i`) the rank is at least the
sum of the ranks of its diagonal entries.  Induction on `n`, writing `M` as a block triangular
matrix with top-left block `oneByOne (M 0 0)` and bottom-right block the `(n-1) × (n-1)` trailing
submatrix, and applying the Sylvester axiom `rk_blockUpper`
(`rk A + rk B ≤ rk (blockUpperFin A B C)`) after reindexing the blocks. -/
theorem rk_le_sum_diag_of_upperTriangular {R : Type} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → M i j = 0) :
    ∑ i : Fin n, rk.rk 1 1 (Work.ORHughesFree.oneByOne (M i i)) ≤ rk.rk n n M := by
  revert h M
  induction n with
  | zero =>
      intro M h
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact rk.rk_nonneg 0 0 M
  | succ n ih =>
      intro M h
      have hM := eq_blockUpperFin_of_upperTriangular M h
      have hA_ut : ∀ i j : Fin n,
          (j : ℕ) < (i : ℕ) → (M.submatrix Fin.castSucc Fin.castSucc) i j = 0 := by
        intro i j hij
        exact h i.castSucc j.castSucc (by simpa using hij)
      have hIH := ih (M.submatrix Fin.castSucc Fin.castSucc) hA_ut
      have hsum : (∑ i : Fin (n + 1), rk.rk 1 1 (oneByOne (M i i)))
          = (∑ i : Fin n, rk.rk 1 1 (oneByOne (M i.castSucc i.castSucc)))
            + rk.rk 1 1 (oneByOne (M (Fin.last n) (Fin.last n))) := by
        rw [Fin.sum_univ_castSucc]
      have hblock := rk.rk_blockUpper (M.submatrix Fin.castSucc Fin.castSucc)
          (oneByOne (M (Fin.last n) (Fin.last n)))
          (M.submatrix Fin.castSucc (fun _ : Fin 1 => Fin.last n))
      calc ∑ i : Fin (n + 1), rk.rk 1 1 (oneByOne (M i i))
          = (∑ i : Fin n, rk.rk 1 1 (oneByOne (M i.castSucc i.castSucc)))
            + rk.rk 1 1 (oneByOne (M (Fin.last n) (Fin.last n))) := hsum
        _ ≤ rk.rk n n (M.submatrix Fin.castSucc Fin.castSucc)
            + rk.rk 1 1 (oneByOne (M (Fin.last n) (Fin.last n))) := add_le_add hIH le_rfl
        _ ≤ rk.rk (n + 1) (n + 1) (blockUpperFin (M.submatrix Fin.castSucc Fin.castSucc)
              (oneByOne (M (Fin.last n) (Fin.last n)))
              (M.submatrix Fin.castSucc (fun _ : Fin 1 => Fin.last n))) := hblock
        _ = rk.rk (n + 1) (n + 1) M := congrArg (rk.rk (n + 1) (n + 1)) hM.symm

end Work.ORHughesFree.RankAPI
