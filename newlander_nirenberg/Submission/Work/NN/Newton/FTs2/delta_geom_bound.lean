import Mathlib

namespace Work.NN.Newton.FTs2

theorem delta_geom_bound (D δ : ℝ) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    D * (1 / ((1 - 7 * δ / 8) - (1 - 15 * δ / 16)) ^ 2) ≤ 256 * D / δ ^ 6 := by
  -- The two linear terms cancel to `δ / 16`.
  have hden : (1 - 7 * δ / 8) - (1 - 15 * δ / 16) = δ / 16 := by ring
  rw [hden]
  -- Since `δ ≤ 1/4`, we have `δ ^ 4 ≤ 1`.
  have hδ4le : δ ^ 4 ≤ 1 := by
    have h : δ ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hδ0.le hδ4 4
    norm_num at h
    linarith
  -- Hence `δ ^ 6 ≤ δ ^ 2` (as `δ ^ 6 = δ ^ 2 * δ ^ 4`).
  have hδ6le : δ ^ 6 ≤ δ ^ 2 := by
    have h6 : δ ^ 6 = δ ^ 2 * δ ^ 4 := by ring
    rw [h6]
    exact mul_le_of_le_one_right (sq_nonneg δ) hδ4le
  -- The left-hand side equals `256 * D / δ ^ 2`.
  have heq : D * (1 / (δ / 16) ^ 2) = 256 * D / δ ^ 2 := by
    field_simp
    ring
  rw [heq]
  -- And `256 * D / δ ^ 2 ≤ 256 * D / δ ^ 6` since `δ ^ 6 ≤ δ ^ 2` and `0 ≤ 256 * D`.
  rw [div_le_div_iff₀ (pow_pos hδ0 2) (pow_pos hδ0 6)]
  exact mul_le_mul_of_nonneg_left hδ6le (by positivity)

end Work.NN.Newton.FTs2
