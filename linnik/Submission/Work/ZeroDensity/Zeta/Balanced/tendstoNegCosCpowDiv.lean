import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

open Filter

/-- As `u → +∞`, the function
`u ↦ -(cos (a u) · u ^ (-s - 1)) / a` tends to `0`, for `Re s > 0` and `a ≠ 0`.

This is a routine decay estimate: the complex power `u ^ (-s - 1)` has modulus
`u ^ (-Re s - 1)`, which tends to `0` at `+∞` because `-Re s - 1 < 0`, while
`cos` is bounded and `a` is a nonzero constant. -/
theorem tendstoNegCosCpowDiv (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun u : ℝ => -(((Real.cos (a * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) / (a : ℂ))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun u : ℝ => u ^ (-s.re - 1) / |a|) ?_ ?_ ?_
  · filter_upwards with u
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    have hnorm : ‖-(((Real.cos (a * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) / (a : ℂ)‖
        = |Real.cos (a * u)| * u ^ (-s.re - 1) / |a| := by
      rw [norm_div, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
      rw [show (-s - 1).re = -s.re - 1 by simp [Complex.sub_re, Complex.neg_re]]
      have e1 : ‖((Real.cos (a * u) : ℝ) : ℂ)‖ = |Real.cos (a * u)| :=
        RCLike.norm_ofReal (K := ℂ) (Real.cos (a * u))
      have e2 : ‖(a : ℂ)‖ = |a| := RCLike.norm_ofReal (K := ℂ) a
      rw [e1, e2]
    rw [hnorm]
    have hrpow_nn : 0 ≤ u ^ (-s.re - 1) := Real.rpow_nonneg hu.le _
    have ha_pos : 0 < |a| := abs_pos.mpr ha
    apply div_le_div_of_nonneg_right _ ha_pos.le
    simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hrpow_nn
  · have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < s.re + 1 by linarith)).div_const (|a|)
    have hh : (fun u : ℝ => u ^ (-s.re - 1) / |a|)
        = fun u : ℝ => u ^ (-(s.re + 1)) / |a| := by
      funext u; rw [show -s.re - 1 = -(s.re + 1) by ring]
    rw [hh]
    simpa using h

end Work.ZeroDensity.Zeta.Balanced
