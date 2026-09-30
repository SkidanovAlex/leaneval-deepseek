import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF.pcsw

/-- `t - a * t ^ (1/12)` tends to `+∞` as `t → +∞`, for any `a > 0`. -/
theorem tendsto_id_sub_rpow (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => t - a * t ^ (1 / 12 : ℝ)) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun t : ℝ => t ^ (1 / 12 : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h2 : Filter.Tendsto (fun t : ℝ => t ^ (11 / 12 : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h3 : Filter.Tendsto (fun t : ℝ => t ^ (11 / 12 : ℝ) - a) Filter.atTop Filter.atTop := by
    have h := h2.atTop_add (tendsto_const_nhds (x := -a))
    simpa only [sub_eq_add_neg] using h
  have h4 : Filter.Tendsto (fun t : ℝ => t ^ (1 / 12 : ℝ) * (t ^ (11 / 12 : ℝ) - a))
      Filter.atTop Filter.atTop := Filter.Tendsto.atTop_mul_atTop₀ h1 h3
  refine Filter.Tendsto.congr' ?_ h4
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have hpow : t ^ (1 / 12 : ℝ) * t ^ (11 / 12 : ℝ) = t := by
    rw [← Real.rpow_add ht (1 / 12) (11 / 12),
      show (1 / 12 : ℝ) + 11 / 12 = 1 by norm_num, Real.rpow_one]
  rw [mul_sub, hpow]
  ring

end Work.BMF.pcsw
