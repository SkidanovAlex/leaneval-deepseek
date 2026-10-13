import Mathlib

namespace Work.WilE5.Operators

theorem rank_eq_of_det_ne_zero_submatrix {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (ι : Fin k → Fin q)
    (h : (M.submatrix id ι).det ≠ 0) : M.rank = k := by
  have h1 : (M.submatrix id ι).rank = k := by
    rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin]
  have h2 : (M.submatrix id ι).rank ≤ M.rank := Matrix.rank_submatrix_le M id ι
  have h3 : M.rank ≤ k := M.rank_le_height
  omega

end Work.WilE5.Operators
