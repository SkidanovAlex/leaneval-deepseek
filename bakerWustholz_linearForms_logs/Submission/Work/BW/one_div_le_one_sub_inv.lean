import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem one_div_le_one_sub_inv (k : ℕ) {x : ℝ} (hx : (k : ℝ) + 2 ≤ x) :
    1 / ((k : ℝ) + 2) ≤ (1 - x⁻¹) * (1 / ((k : ℝ) + 1)) := by
  have hk2 : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hinv : x⁻¹ ≤ 1 / ((k:ℝ) + 2) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hk2 hx
  have h1 : 1 - 1/((k:ℝ)+2) ≤ 1 - x⁻¹ := by linarith
  have h2 : (1 - 1/((k:ℝ)+2)) * (1/((k:ℝ)+1)) = 1/((k:ℝ)+2) := by
    field_simp
    ring
  have h3 : (1 - 1/((k:ℝ)+2)) * (1/((k:ℝ)+1)) ≤ (1 - x⁻¹) * (1/((k:ℝ)+1)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith [h2 ▸ h3]

end Work.BW
