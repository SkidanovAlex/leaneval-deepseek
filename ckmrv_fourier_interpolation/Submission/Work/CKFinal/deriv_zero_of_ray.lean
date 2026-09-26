import Mathlib

namespace Work.CKFinal

open Filter Topology

/-- The point `-exp(-2πy)` (a negative real, viewed in `ℂ`) tends to `0` along the
punctured neighbourhood `{0}ᶜ` as `y → +∞`. -/
theorem tendsto_neg_exp_neg_two_pi :
    Filter.Tendsto (fun y : ℝ => -(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ)) Filter.atTop
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hlin : Filter.Tendsto (fun y : ℝ => 2 * Real.pi * y) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
    have h1 : Filter.Tendsto (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have h2 : Filter.Tendsto (fun y : ℝ => (((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))
        Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa using h2.neg
  · filter_upwards with y
    simp

theorem deriv_zero_of_ray {g : ℂ → ℂ} (hg0 : g 0 = 0) (hgd : DifferentiableAt ℂ g 0)
    (hray : Filter.Tendsto (fun y : ℝ => (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))⁻¹ *
      g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))) Filter.atTop (nhds 0)) :
    deriv g 0 = 0 ∧ Filter.Tendsto (fun q : ℂ => q⁻¹ * g q) (nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ) (nhds 0) := by
  -- The slope of `g` at `0` tends to `deriv g 0`; since `g 0 = 0`, this slope is `q ↦ q⁻¹ * g q`.
  have hslope : Filter.Tendsto (fun q : ℂ => q⁻¹ * g q) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
      (nhds (deriv g 0)) := by
    have h := hgd.hasDerivAt.tendsto_slope_zero
    simpa [hg0, smul_eq_mul] using h
  -- The ray hypothesis is the same slope limit composed with the path `y ↦ -exp(-2πy)`.
  have hcomp : Filter.Tendsto (fun y : ℝ => (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))⁻¹ *
      g (-(((Real.exp (-(2 * Real.pi * y)) : ℝ)) : ℂ))) Filter.atTop (nhds (deriv g 0)) :=
    hslope.comp tendsto_neg_exp_neg_two_pi
  have hzero : deriv g 0 = 0 := tendsto_nhds_unique hcomp hray
  refine ⟨hzero, ?_⟩
  rwa [hzero] at hslope

end Work.CKFinal
