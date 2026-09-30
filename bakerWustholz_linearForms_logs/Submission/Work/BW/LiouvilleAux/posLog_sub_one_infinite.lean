import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.LiouvilleAux

/-- Auxiliary elementary real inequality: for `x ≥ 0` we have
`log⁺ (x + 1) ≤ log⁺ x + log 2`.

Both sides are compared by writing `log⁺ y = log (max 1 y)` for `y ≥ 0`; then the
claim reduces to `log (x + 1) ≤ log (max 1 x · 2)`, i.e. to the elementary
estimate `x + 1 ≤ 2 · max 1 x`, followed by monotonicity of `log`. -/
theorem posLog_add_one_le (x : ℝ) (hx : 0 ≤ x) :
    Real.posLog (x + 1) ≤ Real.posLog x + Real.log 2 := by
  rw [Real.posLog_eq_log_max_one (by linarith : 0 ≤ x + 1),
      Real.posLog_eq_log_max_one hx,
      max_eq_right (by linarith : (1:ℝ) ≤ x + 1)]
  rw [← Real.log_mul (by positivity : max 1 x ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  apply Real.log_le_log (by linarith : (0:ℝ) < x + 1)
  rcases le_or_gt x 1 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h.le]; linarith

theorem posLog_sub_one_infinite {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) (a : K) :
    Real.posLog (v (a - 1)) ≤ Real.posLog (v a) + Real.log 2 := by
  -- Triangle inequality for the absolute value: `v (a - 1) ≤ v a + 1`.
  have hv : v (a - 1) ≤ v a + 1 := by
    have h := AbsoluteValue.sub_le v.1 a 0 1
    rw [sub_zero, zero_sub] at h
    rw [AbsoluteValue.map_neg v.1 1, AbsoluteValue.map_one v.1] at h
    exact h
  -- `v (a - 1) ≥ 0`, so `log⁺` is monotone between `v (a - 1)` and `v a + 1`.
  have hnn : (0:ℝ) ≤ v (a - 1) := AbsoluteValue.nonneg v.1 (a - 1)
  have hmain : Real.posLog (v a + 1) ≤ Real.posLog (v a) + Real.log 2 :=
    posLog_add_one_le (v a) (AbsoluteValue.nonneg v.1 a)
  exact le_trans (Real.posLog_le_posLog (by linarith) hv) hmain

end Work.BW.LiouvilleAux
