import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

lemma cell_len_bounds {H a b p : ℝ} (hH : 0 < H) (ha : 0 < a) (h5b : 5 * b ≤ 7 * a) (hap : a ≤ p) (hpb : p ≤ b) : 0 < H / p ∧ H / p ≤ H / a ∧ H / p ≤ 2 * (H / a) ∧ H / a ≤ 2 * (H / p) ∧ 3 * H / (2 * a) ≤ 2 * (H / a) := by
  have hp : 0 < p := lt_of_lt_of_le ha hap
  -- from `5 * b ≤ 7 * a` and `p ≤ b` we get `p ≤ (7/5) * a ≤ 2 * a`
  have hp2a : p ≤ 2 * a := by linarith
  have hpa : H / p ≤ H / a := div_le_div_of_nonneg_left hH.le ha hap
  have hHa : 0 ≤ H / a := div_nonneg hH.le ha.le
  refine ⟨div_pos hH hp, hpa, ?_, ?_, ?_⟩
  · linarith
  · rw [div_le_iff₀ ha]
    rw [show 2 * (H / p) * a = 2 * H * a / p by ring]
    rw [le_div_iff₀ hp]
    nlinarith [mul_le_mul_of_nonneg_left hp2a hH.le]
  · have h : 3 * H / (2 * a) = (3 / 2) * (H / a) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right (by norm_num) hHa

end Work.BMF.SD
