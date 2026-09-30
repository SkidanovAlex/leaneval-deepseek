import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

/-- `t * exp(-t/2 + a * t^(1/12)) → 0` as `t → ∞` for any real `a`.

The exponential factor `exp(a * t^(1/12))` grows slower than any linear exponential `exp(t/4)`,
so eventually the whole integrand is dominated by `t * exp(-t/4)`, which tends to `0`. -/
theorem tendsto_mul_exp_sub_rpow (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => t * Real.exp (-t / 2 + a * t ^ (1 / 12 : ℝ))) Filter.atTop (nhds 0) := by
  -- `ha` is not needed for the bound, but we keep the hypothesis; use it to avoid the
  -- unused-variable linter firing on the fixed statement.
  have _ha : 0 < a := ha
  -- The dominating function `t * exp(-t/4)` tends to `0`.
  have hU : Filter.Tendsto (fun t : ℝ => t * Real.exp (-(1 / 4) * t)) Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 4) (by norm_num)
  -- `t^(11/12) → ∞`, so eventually `4*a ≤ t^(11/12)`.
  have hpow : Filter.Tendsto (fun t : ℝ => t ^ ((11 : ℝ) / 12)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  -- Eventually `a * t^(1/12) ≤ t / 4`.
  have hbound : ∀ᶠ t : ℝ in Filter.atTop, a * t ^ (1 / 12 : ℝ) ≤ t / 4 := by
    filter_upwards [hpow.eventually_ge_atTop (4 * a), Filter.eventually_gt_atTop (0 : ℝ)]
      with t ht4 ht0
    have h1 : t ^ ((11 : ℝ) / 12) * t ^ (1 / 12 : ℝ) = t := by
      rw [← Real.rpow_add ht0, show (11 : ℝ) / 12 + 1 / 12 = 1 by norm_num, Real.rpow_one]
    have h2 : 4 * a * t ^ (1 / 12 : ℝ) ≤ t := by
      calc 4 * a * t ^ (1 / 12 : ℝ) ≤ t ^ ((11 : ℝ) / 12) * t ^ (1 / 12 : ℝ) :=
            mul_le_mul_of_nonneg_right ht4 (Real.rpow_nonneg ht0.le _)
        _ = t := h1
    linarith
  -- Squeeze: `0 ≤ f t ≤ t * exp(-t/4)` eventually, and the upper bound tends to `0`.
  refine squeeze_zero' ?_ ?_ hU
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg ht (Real.exp_nonneg _)
  · filter_upwards [hbound, Filter.eventually_ge_atTop (0 : ℝ)] with t hb ht
    apply mul_le_mul_of_nonneg_left _ ht
    apply Real.exp_le_exp.mpr
    linarith

end Work.BMF.pcsw
