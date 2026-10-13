import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- Quantitative Lipschitz bound for `x ↦ 1 / x ^ 2` on `[1, ∞)`, with the
constant measured by `min U W`: for `U, W ≥ 1`,
`|1 / U ^ 2 - 1 / W ^ 2| ≤ 2 * |U - W| / (min U W) ^ 3`. -/
lemma A0_inv_sq_sub_le {U W : ℝ} (hU : 1 ≤ U) (hW : 1 ≤ W) :
    |1 / U ^ 2 - 1 / W ^ 2| ≤ 2 * |U - W| / (min U W) ^ 3 := by
  have hU0 : 0 < U := by linarith
  have hW0 : 0 < W := by linarith
  have hkey : 1 / U ^ 2 - 1 / W ^ 2 = (W - U) * (W + U) / (U ^ 2 * W ^ 2) := by
    field_simp
    ring
  have hsq : |1 / U ^ 2 - 1 / W ^ 2| = |U - W| * ((U + W) / (U ^ 2 * W ^ 2)) := by
    rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < U ^ 2 * W ^ 2), abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < W + U), abs_sub_comm]
    ring
  have hmain : (U + W) / (U ^ 2 * W ^ 2) ≤ 2 / (min U W) ^ 3 := by
    rcases le_total U W with h | h
    · rw [min_eq_left h, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : U * U ≤ W * W := mul_self_le_mul_self hU0.le h
      have h2 : U * W ≤ W * W := mul_le_mul_of_nonneg_right h hW0.le
      have h3 : (U + W) * U ≤ 2 * W ^ 2 := by nlinarith [h1, h2]
      have h4 : (U + W) * U * U ^ 2 ≤ 2 * W ^ 2 * U ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg U)
      nlinarith [h4]
    · rw [min_eq_right h, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : W * W ≤ U * U := mul_self_le_mul_self hW0.le h
      have h2 : W * U ≤ U * U := mul_le_mul_of_nonneg_right h hU0.le
      have h3 : (U + W) * W ≤ 2 * U ^ 2 := by nlinarith [h1, h2]
      have h4 : (U + W) * W * W ^ 2 ≤ 2 * U ^ 2 * W ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg W)
      nlinarith [h4]
  calc |1 / U ^ 2 - 1 / W ^ 2| = |U - W| * ((U + W) / (U ^ 2 * W ^ 2)) := hsq
    _ ≤ |U - W| * (2 / (min U W) ^ 3) := mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
    _ = 2 * |U - W| / (min U W) ^ 3 := by ring

end Work.ConstructionInstance
