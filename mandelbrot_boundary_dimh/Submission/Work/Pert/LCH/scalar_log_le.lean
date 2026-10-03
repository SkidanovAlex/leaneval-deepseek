import Mathlib

namespace Work.Pert.LCH

/-- For `w ∈ [1/5, 1]` one has `5 (w - 1) ≤ log w`.
This follows from `1 - 1/w ≤ log w` together with the elementary estimate
`5 (w - 1) ≤ 1 - 1/w` valid on `[1/5, 1]`. -/
private lemma five_mul_sub_one_le_log {w : ℝ} (h1 : 1 / 5 ≤ w) (h2 : w ≤ 1) :
    5 * (w - 1) ≤ Real.log w := by
  have hw : 0 < w := by linarith
  have hlog : 1 - w⁻¹ ≤ Real.log w := Real.one_sub_inv_le_log_of_pos hw
  have hstep : 5 * (w - 1) ≤ 1 - w⁻¹ := by
    have hprod : 0 ≤ (5 * w - 1) * (1 - w) := by
      apply mul_nonneg <;> linarith
    have hinv : 1 - w⁻¹ = (w - 1) / w := by
      rw [inv_eq_one_div]; field_simp
    rw [hinv, le_div_iff₀ hw]
    nlinarith [hprod]
  linarith

theorem scalar_log_le {b u : ℝ} (hb : b ≤ 1) (hu : 0 < u) (hu8 : u ≤ 8) :
    b * u ≤ 2 * (2 + Real.log (2 + u)) := by
  -- `log 10 > 2`, obtained from `exp 1 < 3` via `exp 2 = (exp 1)^2 < 9 < 10`.
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    rw [← Real.log_exp 2, Real.log_lt_log_iff (Real.exp_pos 2) (by norm_num)]
    have h2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h2]
    have hlt : Real.exp 1 * Real.exp 1 < 3 * Real.exp 1 :=
      mul_lt_mul_of_pos_right Real.exp_one_lt_three (Real.exp_pos 1)
    have hlt2 : (3 : ℝ) * Real.exp 1 < 3 * 3 :=
      mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num)
    linarith
  -- Reduction to the scalar bound `u ≤ 2 * (2 + log (2 + u))` on `0 < u ≤ 8`.
  have hmain : u ≤ 2 * (2 + Real.log (2 + u)) := by
    have hwpos : 0 < (2 + u) / 10 := by linarith
    have hw1 : 1 / 5 ≤ (2 + u) / 10 := by linarith
    have hw2 : (2 + u) / 10 ≤ 1 := by linarith
    have hlogw := five_mul_sub_one_le_log hw1 hw2
    have hlogx : Real.log (2 + u) = Real.log 10 + Real.log ((2 + u) / 10) := by
      have h10 : (2 : ℝ) + u = 10 * ((2 + u) / 10) := by ring
      conv_lhs => rw [h10]
      exact Real.log_mul (by norm_num) (ne_of_gt hwpos)
    rw [hlogx]
    nlinarith [hlogw, hlog10]
  rcases le_or_gt b 0 with hb0 | hbpos
  · -- `b ≤ 0` makes the left-hand side nonpositive while the right-hand side is positive.
    have h1 : b * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 (le_of_lt hu)
    have h2 : 0 < Real.log (2 + u) := Real.log_pos (by linarith)
    linarith
  · -- `0 < b ≤ 1` gives `b * u ≤ u`, and `u` is bounded above by `hmain`.
    have h1 : b * u ≤ u := mul_le_of_le_one_left (le_of_lt hu) hb
    linarith

end Work.Pert.LCH
