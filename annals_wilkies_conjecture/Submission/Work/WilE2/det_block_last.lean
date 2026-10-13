import Mathlib
import Submission.Work.WilE2.det_fromBlocks_eq

namespace Work.WilE2

theorem det_block_last {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (c b : Fin n → ℝ)
    (h11 : ∀ j k : Fin n, M (Fin.castSucc j) (Fin.castSucc k) = Q j k)
    (h12 : ∀ j : Fin n, M (Fin.castSucc j) (Fin.last n) = c j)
    (h21 : ∀ k : Fin n, M (Fin.last n) (Fin.castSucc k) = b k)
    (h22 : M (Fin.last n) (Fin.last n) = -1) :
    M.det = -(Q + Matrix.vecMulVec c b).det := by
  -- Reindex `Fin (n+1)` as `Fin n ⊕ Fin 1`: the block matrix structure is then literal.
  have hM : M.submatrix (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) =
      Matrix.fromBlocks Q (Matrix.of (fun i (_ : Fin 1) => c i))
        (Matrix.of (fun (_ : Fin 1) j => b j))
        (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => (-1 : ℝ))) := by
    ext i j
    rcases i with x | x <;> rcases j with y | y
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact h11 x y
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
      fin_cases y
      exact h12 x
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
      fin_cases x
      exact h21 y
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right,
        Matrix.of_apply]
      fin_cases x
      fin_cases y
      exact h22
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := n) (n := 1)) M, hM]
  exact det_fromBlocks_eq Q c b

end Work.WilE2
