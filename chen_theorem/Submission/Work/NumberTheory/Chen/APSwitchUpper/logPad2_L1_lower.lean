import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- The Taylor/geometric lower bound for `log ((1+s)/(1-s))`: for `0 ≤ s < 1`,
`2s + (2/3)s³ ≤ log ((1+s)/(1-s))`.  This is `Real.sum_range_le_log_div` truncated
after the `i = 0, 1` terms, multiplied by `2`. -/
lemma log_pad_aux (s : ℝ) (h0 : 0 ≤ s) (h1 : s < 1) :
    2 * s + (2 / 3 : ℝ) * s ^ 3 ≤ Real.log ((1 + s) / (1 - s)) := by
  have h := Real.sum_range_le_log_div h0 h1 2
  have hsum : (∑ i ∈ Finset.range 2, s ^ (2 * i + 1) / (2 * i + 1)) = s + s ^ 3 / 3 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum] at h
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  calc 2 * s + (2 / 3 : ℝ) * s ^ 3 = 2 * (s + s ^ 3 / 3) := by ring
    _ ≤ 2 * (1 / 2 * Real.log ((1 + s) / (1 - s))) := h2
    _ = Real.log ((1 + s) / (1 - s)) := by ring

theorem logPad2_L1_lower (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3
      ≤ Real.log (3 / (u - 1)) := by
  set s : ℝ := (4 - u) / (u + 2) with hs
  have hu2 : (0 : ℝ) < u + 2 := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg (by linarith) (by linarith)
  have hs1 : s < 1 := by rw [hs, div_lt_one hu2]; linarith
  have hkey := log_pad_aux s hs0 hs1
  have harg : (1 + s) / (1 - s) = 3 / (u - 1) := by
    rw [hs]
    have hd1 : (1 : ℝ) - (4 - u) / (u + 2) ≠ 0 := by
      have h : (1 : ℝ) - (4 - u) / (u + 2) = 2 * (u - 1) / (u + 2) := by
        field_simp; ring
      rw [h]; apply div_ne_zero (by linarith) (by linarith)
    have hd2 : (u : ℝ) - 1 ≠ 0 := by linarith
    rw [div_eq_div_iff hd1 hd2]
    field_simp
    ring
  rw [harg] at hkey
  exact hkey

end Work.NumberTheory.Chen.APSwitchUpper
