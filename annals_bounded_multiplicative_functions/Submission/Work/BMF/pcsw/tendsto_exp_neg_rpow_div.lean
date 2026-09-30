import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.pcsw

theorem tendsto_exp_neg_rpow_div (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-a * t ^ (1 / 12 : ℝ)) / t) Filter.atTop (nhds 0) := by
  -- The exponent `a * t^(1/12) → atTop`, so `exp (-(a * t^(1/12))) → 0`.
  have hg : Filter.Tendsto (fun t : ℝ => a * t ^ (1 / 12 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 12)).const_mul_atTop ha
  have h1 : Filter.Tendsto (fun t : ℝ => Real.exp (-(a * t ^ (1 / 12 : ℝ))))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hg
  have h1' : Filter.Tendsto (fun t : ℝ => Real.exp (-a * t ^ (1 / 12 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [neg_mul] using h1
  -- The whole expression is a product of two null sequences.
  have h2 : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have := h1'.mul h2
  simpa [div_eq_mul_inv] using this

end Work.BMF.pcsw
