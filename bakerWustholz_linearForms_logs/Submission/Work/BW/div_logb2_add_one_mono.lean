import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Monotonicity of `x ↦ x / (log₂ x + 1)` on `[Real.exp 1, ∞)`. -/
theorem div_logb2_add_one_mono {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    x / (Real.logb 2 x + 1) ≤ y / (Real.logb 2 y + 1) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  have hy1 : (1 : ℝ) ≤ y := le_trans hx1 hxy
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- antitone step: `log y / y ≤ log x / x`
  have hanti : Real.log y / y ≤ Real.log x / x :=
    Real.log_div_self_antitoneOn hx (le_trans hx hxy) hxy
  have hlog : Real.log y * x ≤ Real.log x * y :=
    (div_le_div_iff₀ hypos hxpos).mp hanti
  have h2 : x * Real.log 2 ≤ y * Real.log 2 :=
    mul_le_mul_of_nonneg_right hxy (le_of_lt hlog2pos)
  have hsum : x * (Real.log y + Real.log 2) ≤ y * (Real.log x + Real.log 2) := by
    nlinarith [hlog, h2]
  -- rewrite `Real.log z + Real.log 2 = Real.log 2 * (Real.logb 2 z + 1)`
  have e1 : Real.log y + Real.log 2 = Real.log 2 * (Real.logb 2 y + 1) := by
    rw [← Real.log_div_log (x := y)]
    field_simp
  have e2 : Real.log x + Real.log 2 = Real.log 2 * (Real.logb 2 x + 1) := by
    rw [← Real.log_div_log (x := x)]
    field_simp
  rw [e1, e2] at hsum
  have hmul : Real.log 2 * (x * (Real.logb 2 y + 1))
      ≤ Real.log 2 * (y * (Real.logb 2 x + 1)) := by
    nlinarith [hsum]
  have hmain : x * (Real.logb 2 y + 1) ≤ y * (Real.logb 2 x + 1) :=
    le_of_mul_le_mul_left hmul hlog2pos
  have hxden : 0 < Real.logb 2 x + 1 := by
    have : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
    linarith
  have hyden : 0 < Real.logb 2 y + 1 := by
    have : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy1
    linarith
  rw [div_le_div_iff₀ hxden hyden]
  exact hmain

end Work.BW
