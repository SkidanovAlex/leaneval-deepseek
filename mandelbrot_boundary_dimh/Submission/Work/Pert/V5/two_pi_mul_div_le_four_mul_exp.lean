import Mathlib

namespace Work.Pert.V5

/-- Auxiliary: `exp 1 < 3` yields `1/3 ≤ exp (-1)`. -/
private lemma one_third_le_exp_neg_one : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
  have h := one_div_lt_one_div_of_lt (Real.exp_pos 1) Real.exp_one_lt_three
  rw [Real.exp_neg]
  simpa [one_div] using h.le

/-- Auxiliary numeric bound: `2π/9 ≤ 4 e^{-1}`. -/
private lemma two_pi_div_nine_le_four_exp_neg_one : 2 * Real.pi / 9 ≤ 4 * Real.exp (-1) := by
  nlinarith [Real.pi_lt_four, one_third_le_exp_neg_one]

/-- For `0 ≤ u ≤ 1/4` and `D > 0`, the ratio `2πD/(2πD+9)` is dominated by `4D e^{-πu}`. -/
theorem two_pi_mul_div_le_four_mul_exp {u D : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) (hD : 0 < D) :
    2 * Real.pi * D / (2 * Real.pi * D + 9) ≤ 4 * D * Real.exp (-(Real.pi * u)) := by
  -- `π * u ≤ 1`, so `exp (-1) ≤ exp (-(π u))`.
  have hpiu : Real.pi * u ≤ 1 := by
    nlinarith [hu0, hu1, Real.pi_pos, Real.pi_lt_four]
  have hexp_ge : Real.exp (-1) ≤ Real.exp (-(Real.pi * u)) :=
    Real.exp_le_exp.mpr (by linarith)
  -- Hence `2π/9 ≤ 4 * exp (-(π u))`.
  have hmain : 2 * Real.pi / 9 ≤ 4 * Real.exp (-(Real.pi * u)) :=
    le_trans two_pi_div_nine_le_four_exp_neg_one
      (mul_le_mul_of_nonneg_left hexp_ge (by norm_num : (0 : ℝ) ≤ 4))
  -- Drop the `9` in the denominator.
  have h1 : 2 * Real.pi * D / (2 * Real.pi * D + 9) ≤ 2 * Real.pi * D / 9 :=
    div_le_div_of_nonneg_left (by nlinarith [Real.pi_pos, hD.le]) (by norm_num)
      (by nlinarith [Real.pi_pos])
  calc 2 * Real.pi * D / (2 * Real.pi * D + 9)
      ≤ 2 * Real.pi * D / 9 := h1
    _ = (2 * Real.pi / 9) * D := by ring
    _ ≤ (4 * Real.exp (-(Real.pi * u))) * D :=
        mul_le_mul_of_nonneg_right hmain (le_of_lt hD)
    _ = 4 * D * Real.exp (-(Real.pi * u)) := by ring

end Work.Pert.V5
