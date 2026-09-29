import Mathlib

/-!
# A grid value of the sine at the `256`-th grid

`sin (61 * π / 256) = sin (244 * π / 1024) ∈ [0.678, 0.6812]`.

The argument is elementary and avoids any certified-numerics machinery:

* `61 * π / 256` is bracketed between the two rationals
  `191637112 / 256000000` and `191637173 / 256000000` using `Real.pi_gt_d6` and `Real.pi_lt_d6`;
* the lower bound is the sharp cubic bound `Real.sin_ge_sub_cube`
  (`x - x³/6 ≤ sin x`), combined with monotonicity of the monomials on `[0, b]`;
* the upper bound is the Taylor bound `Real.sin_bound`
  (`|sin x - (x - x³/6)| ≤ |x|⁵/100`), again with monomial monotonicity.
-/

namespace Work.CNum.DAux

theorem SinGrid256 : (0.678 : ℝ) ≤ Real.sin (61 * Real.pi / 256) ∧
    Real.sin (61 * Real.pi / 256) ≤ (0.6812 : ℝ) := by
  have hπlo : (3141592 : ℝ) / 1000000 < Real.pi := by linarith [Real.pi_gt_d6]
  have hπhi : Real.pi < (3141593 : ℝ) / 1000000 := by linarith [Real.pi_lt_d6]
  set x : ℝ := 61 * Real.pi / 256 with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hlo : (191637112 : ℝ) / 256000000 ≤ x := by
    rw [hx]
    have h : (61 : ℝ) * (3141592 / 1000000 : ℝ) < 61 * Real.pi :=
      mul_lt_mul_of_pos_left hπlo (by norm_num)
    have h2 : (61 : ℝ) * (3141592 / 1000000 : ℝ) / 256 ≤ 61 * Real.pi / 256 :=
      div_le_div_of_nonneg_right h.le (by norm_num)
    have h3 : (61 : ℝ) * (3141592 / 1000000 : ℝ) / 256 = 191637112 / 256000000 := by norm_num
    rw [h3] at h2
    exact h2
  have hhi : x ≤ (191637173 : ℝ) / 256000000 := by
    rw [hx]
    have h : (61 : ℝ) * Real.pi < 61 * (3141593 / 1000000 : ℝ) :=
      mul_lt_mul_of_pos_left hπhi (by norm_num)
    have h2 : 61 * Real.pi / 256 ≤ (61 : ℝ) * (3141593 / 1000000 : ℝ) / 256 :=
      div_le_div_of_nonneg_right h.le (by norm_num)
    have h3 : (61 : ℝ) * (3141593 / 1000000 : ℝ) / 256 = 191637173 / 256000000 := by norm_num
    rw [h3] at h2
    exact h2
  have hx1 : x ≤ 1 := by
    have h2 : (61 : ℝ) * Real.pi / 256 ≤ 61 * (3141593 / 1000000 : ℝ) / 256 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hπhi.le (by norm_num))
        (by norm_num)
    have h3 : (61 : ℝ) * (3141593 / 1000000 : ℝ) / 256 ≤ 1 := by norm_num
    linarith
  have hlow : (0.678 : ℝ) ≤ Real.sin x := by
    have h1 : x - x ^ 3 / 6 ≤ Real.sin x := Real.sin_ge_sub_cube hx0
    have hx3 : x ^ 3 ≤ ((191637173 : ℝ) / 256000000) ^ 3 := pow_le_pow_left₀ hx0 hhi 3
    have hnum : (0.678 : ℝ) ≤
        (191637112 : ℝ) / 256000000 - ((191637173 : ℝ) / 256000000) ^ 3 / 6 := by norm_num
    linarith
  have hup : Real.sin x ≤ (0.6812 : ℝ) := by
    have hb := Real.sin_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rw [abs_of_nonneg hx0] at hb
    have h1 : Real.sin x - (x - x ^ 3 / 6) ≤ x ^ 5 / 100 := by
      linarith [le_abs_self (Real.sin x - (x - x ^ 3 / 6)), hb]
    have ha3 : ((191637112 : ℝ) / 256000000) ^ 3 ≤ x ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hlo 3
    have hb5 : x ^ 5 ≤ ((191637173 : ℝ) / 256000000) ^ 5 := pow_le_pow_left₀ hx0 hhi 5
    have hnum : (191637173 : ℝ) / 256000000 - ((191637112 : ℝ) / 256000000) ^ 3 / 6
        + ((191637173 : ℝ) / 256000000) ^ 5 / 100 ≤ (0.6812 : ℝ) := by norm_num
    linarith
  exact ⟨hlow, hup⟩

end Work.CNum.DAux
