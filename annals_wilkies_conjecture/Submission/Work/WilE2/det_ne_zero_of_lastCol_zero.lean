import Mathlib

namespace Work.WilE2

theorem det_ne_zero_of_lastCol_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (h0 : ∀ i : Fin n, M (Fin.castSucc i) (Fin.last n) = 0)
    (hA : (M.submatrix Fin.castSucc Fin.castSucc).det ≠ 0)
    (hc : M (Fin.last n) (Fin.last n) ≠ 0) : M.det ≠ 0 := by
  -- Reindex `Fin (n+1)` as `Fin n ⊕ Fin 1`: the top-right block of `M` is then the zero block.
  have hM : M.submatrix (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1)) =
      Matrix.fromBlocks (M.submatrix Fin.castSucc Fin.castSucc)
        (0 : Matrix (Fin n) (Fin 1) ℝ)
        (Matrix.of (fun (_ : Fin 1) j => M (Fin.last n) (Fin.castSucc j)))
        (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => M (Fin.last n) (Fin.last n))) := by
    ext i j
    rcases i with x | x <;> rcases j with y | y
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      fin_cases y
      exact h0 x
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      fin_cases x
      rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
        finSumFinEquiv_apply_right]
      fin_cases x
      fin_cases y
      rfl
  have hdet : M.det = (M.submatrix Fin.castSucc Fin.castSucc).det * M (Fin.last n) (Fin.last n) := by
    rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := n) (n := 1)) M, hM,
      Matrix.det_fromBlocks_zero₁₂]
    congr 1
    rw [Matrix.det_fin_one]
    rfl
  rw [hdet]
  exact mul_ne_zero hA hc

end Work.WilE2
