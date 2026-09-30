import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Filter Asymptotics

/-- For `s > 0` and any real `C`, the quantity `X ^ s / log X` is eventually at least `C`:
the power function dominates the logarithm at infinity. -/
theorem qe6_ratio_atTop (s C : ℝ) (hs : 0 < s) :
    ∀ᶠ X : ℝ in Filter.atTop, C ≤ X ^ s / Real.log X := by
  rcases le_or_gt C 0 with hC | hC
  · -- `C ≤ 0`: the ratio is eventually nonnegative.
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with X hX
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
    have hpow : 0 ≤ X ^ s := Real.rpow_nonneg (by linarith) s
    exact le_trans hC (div_nonneg hpow hlog)
  · -- `0 < C`: use `log =o(X ^ s)`, so `log X / X ^ s` is eventually `< 1 / C`.
    have hlit := (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
    have hev : ∀ᶠ X : ℝ in Filter.atTop, Real.log X / X ^ s < 1 / C :=
      (tendsto_order.1 hlit).2 (1 / C) (by positivity)
    filter_upwards [hev, Filter.eventually_gt_atTop (1:ℝ)] with X hlt hX
    have hlogpos : 0 < Real.log X := Real.log_pos hX
    have hpowpos : 0 < X ^ s := Real.rpow_pos_of_pos (by linarith) s
    have h1 : Real.log X < 1 / C * X ^ s := by
      have hh := mul_lt_mul_of_pos_right hlt hpowpos
      simp only [div_eq_mul_inv] at hh
      rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hpowpos), mul_one] at hh
    have h2 : C * Real.log X < X ^ s := by
      have hh := mul_lt_mul_of_pos_left h1 hC
      rw [← mul_assoc, mul_one_div, div_self hC.ne', one_mul] at hh
      exact hh
    exact le_of_lt ((lt_div_iff₀ hlogpos).mpr h2)

end Work.N8
