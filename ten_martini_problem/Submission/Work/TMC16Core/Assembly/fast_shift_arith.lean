import Mathlib

namespace Work.TMC16Core.Assembly

lemma fast_shift_arith {a b Δ : ℝ} (ha : 1 ≤ a) (hΔ0 : 0 ≤ Δ)
    (hb : (8 * a) ^ 9 ≤ b) (hΔb : Δ < 1 / b) :
    ((4 * Real.rpow b (8 / 9) + 8 * a + 4) / a + 1 / 2) * Δ ≤ 2 / a ^ 2 := by
  show ((4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) / a + 1 / 2) * Δ ≤ 2 / a ^ 2
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h8a : 0 < 8 * a := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hb1 : 1 ≤ b := by
    have h1 : (1:ℝ) ≤ (8 * a) ^ 9 := by
      have : (1:ℝ) ≤ 8 * a := by linarith
      calc (1:ℝ) = 1 ^ 9 := by norm_num
        _ ≤ (8 * a) ^ 9 := pow_le_pow_left₀ (by norm_num) this 9
    linarith
  have hb91 : (8 * a) ^ (9:ℝ) = (8 * a) ^ 9 := Real.rpow_natCast (8 * a) 9
  have hbpow : 8 * a ≤ b ^ (1 / 9 : ℝ) := by
    have hb9' : (8 * a) ^ (9:ℝ) ≤ b := by rw [hb91]; exact hb
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (8 * a) ^ (9:ℝ)) hb9'
      (by norm_num : (0:ℝ) ≤ 1/9)
    rw [← Real.rpow_mul (le_of_lt h8a) 9 (1/9),
      show ((9:ℝ) * (1/9)) = 1 by norm_num, Real.rpow_one] at h
    exact h
  have hb89 : 0 ≤ b ^ (8 / 9 : ℝ) := Real.rpow_nonneg (le_of_lt hb0) _
  have hmul : b ^ (8 / 9 : ℝ) * b ^ (1 / 9 : ℝ) = b := by
    rw [← Real.rpow_add hb0 (8/9) (1/9), show ((8:ℝ)/9 + 1/9) = 1 by norm_num, Real.rpow_one]
  have hkey : 4 * b ^ (8 / 9 : ℝ) * a ≤ b / 2 := by
    nlinarith [hmul, hbpow, hb89, ha0]
  have hbig : 8 * a ^ 2 + 4 * a + a ^ 2 / 2 ≤ (3 / 2) * b := by
    have h9 : (8 * a) ^ 9 = 134217728 * a ^ 9 := by ring
    rw [h9] at hb
    have ha2 : (1:ℝ) ≤ a ^ 2 := by nlinarith
    have h9ge : a ^ 2 ≤ a ^ 9 := by
      have := pow_le_pow_right₀ ha (show (2:ℕ) ≤ 9 by norm_num)
      simpa using this
    nlinarith [hb, h9ge, ha2]
  have hmain : (4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) * a + a ^ 2 / 2 ≤ 2 * b := by
    nlinarith [hkey, hbig, ha0]
  have hΔle : Δ ≤ 1 / b := le_of_lt hΔb
  have hcoef : 0 ≤ (4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) / a + 1 / 2 := by
    have h1 : 0 ≤ (4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) / a :=
      div_nonneg (by linarith [hb89, ha0]) (le_of_lt ha0)
    linarith
  refine le_trans (mul_le_mul_of_nonneg_left hΔle hcoef) ?_
  have hgoal : ((4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) / a + 1 / 2) * (1 / b)
      = ((4 * b ^ (8 / 9 : ℝ) + 8 * a + 4) * a + a ^ 2 / 2) / (a ^ 2 * b) := by
    field_simp
  rw [hgoal, div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2 * b)]
  rw [show (2 / a ^ 2) * (a ^ 2 * b) = 2 * b by field_simp]
  exact hmain

end Work.TMC16Core.Assembly
