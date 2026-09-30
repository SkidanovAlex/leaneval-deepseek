import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If a real `n × k` matrix has orthonormal columns (i.e. `Bᵀ B = 1`), then there can be at
most `n` of them: `k ≤ n`.  Proof via ranks: `k = rank (Bᵀ B) ≤ rank (Bᵀ) = rank B ≤ n`. -/
theorem card_le_of_orthonormal {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) (hB : B.transpose * B = 1) : k ≤ n := by
  have h1 : (B.transpose * B).rank = k := by rw [hB, Matrix.rank_one, Fintype.card_fin]
  have h2 : (B.transpose * B).rank ≤ B.rank := by
    calc (B.transpose * B).rank ≤ B.transpose.rank := Matrix.rank_mul_le_left B.transpose B
      _ = B.rank := Matrix.rank_transpose B
  have h3 : B.rank ≤ n := Matrix.rank_le_height B
  omega

end Work.BW
