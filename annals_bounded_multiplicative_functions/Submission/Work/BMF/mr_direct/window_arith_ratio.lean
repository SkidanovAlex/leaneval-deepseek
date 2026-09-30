import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem window_arith_ratio (X₁ X₂ K : ℝ) (hX₁ : 16 ≤ X₁) (hX₁₂ : X₁ ≤ X₂) (hK : 0 ≤ K) :
    K * (((⌊X₂⌋₊ : ℕ) : ℝ) + (((⌈X₁⌉₊ : ℕ) : ℝ) - 1)) *
      (1 / (((⌊X₂⌋₊ : ℕ) : ℝ)) + 1 / (((⌈X₁⌉₊ : ℕ) : ℝ))) ≤ 6 * K * (X₂ / X₁) := by
  -- Abbreviate the numerator data coming from the floor and ceiling.
  set a : ℝ := ((⌊X₂⌋₊ : ℕ) : ℝ) with ha
  set b : ℝ := ((⌈X₁⌉₊ : ℕ) : ℝ) with hb
  have hX₁pos : 0 < X₁ := by linarith
  have hX₂pos : 0 < X₂ := by linarith
  -- Bounds on a = floor X₂.
  have ha_le : a ≤ X₂ := by rw [ha]; exact Nat.floor_le (le_of_lt hX₂pos)
  have ha_ge : 16 ≤ a := by
    rw [ha]
    have h1 : 16 ≤ ⌊X₁⌋₊ := Nat.le_floor hX₁
    have h2 : ⌊X₁⌋₊ ≤ ⌊X₂⌋₊ := Nat.floor_mono hX₁₂
    exact_mod_cast le_trans h1 h2
  have ha_ge' : X₂ - 1 ≤ a := by
    rw [ha]
    have := Nat.lt_floor_add_one X₂
    linarith
  -- Bounds on b = ceil X₁.
  have hb_ge : 16 ≤ b := by
    rw [hb]
    exact le_trans hX₁ (Nat.le_ceil X₁)
  have hb_ge' : X₁ ≤ b := by rw [hb]; exact Nat.le_ceil X₁
  have hb_le : b ≤ X₁ + 1 := by
    rw [hb]
    have := Nat.ceil_lt_add_one (le_of_lt hX₁pos)
    linarith
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  -- Drop the `-1` in the second factor.
  have h2 : (a + (b - 1)) * (1 / a + 1 / b) ≤ (a + b) * (1 / a + 1 / b) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  -- Expand the product with the enlarged factor.
  have expand : (a + b) * (1 / a + 1 / b) = a / b + b / a + 2 := by
    rw [mul_add, mul_one_div, mul_one_div, add_div, add_div, div_self (ne_of_gt ha_pos),
        div_self (ne_of_gt hb_pos)]
    ring
  rw [expand] at h2
  -- Bound a / b ≤ X₂ / X₁.
  have hab : a / b ≤ X₂ / X₁ := by
    rw [div_le_iff₀ hb_pos, div_mul_eq_mul_div, le_div_iff₀ hX₁pos]
    nlinarith [ha_le, hb_ge']
  -- Bound b / a ≤ 17/15.
  have hba : b / a ≤ 17 / 15 := by
    rw [div_le_iff₀ ha_pos]
    linarith
  -- Combine.
  have hsum : a / b + b / a + 2 ≤ 6 * (X₂ / X₁) := by
    have ht1 : 1 ≤ X₂ / X₁ := by
      rw [le_div_iff₀ hX₁pos]
      linarith
    linarith
  have hinner : (a + (b - 1)) * (1 / a + 1 / b) ≤ 6 * (X₂ / X₁) := le_trans h2 hsum
  -- Multiply by the nonnegative factor K.
  calc K * (a + (b - 1)) * (1 / a + 1 / b)
      = K * ((a + (b - 1)) * (1 / a + 1 / b)) := by ring
    _ ≤ K * (6 * (X₂ / X₁)) := mul_le_mul_of_nonneg_left hinner hK
    _ = 6 * K * (X₂ / X₁) := by ring

end Work.BMF.mr_direct
