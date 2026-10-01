import Mathlib

namespace Work.ZeroDensity.Ingham

open MeasureTheory

/-- The imaginary part of the moving denominator is `R - u.im`, independent of `x`. -/
private lemma im_denom (x R : ℝ) (u : ℂ) :
    ((x : ℂ) + R * Complex.I - u).im = R - u.im := by
  simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re]

theorem horizontalPoleDecayAdd (a u : ℂ) (p q : ℝ) :
    Filter.Tendsto (fun R : ℝ => ∫ x in p..q, a / ((x : ℂ) + R * Complex.I - u)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · filter_upwards with R
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_gt_atTop |u.im|] with R hR
    have hpos : 0 < R - |u.im| := sub_pos.mpr hR
    have hbound : ∀ x ∈ Set.uIoc p q,
        ‖a / ((x : ℂ) + R * Complex.I - u)‖ ≤ ‖a‖ / (R - |u.im|) := by
      intro x _
      rw [norm_div]
      apply div_le_div_of_nonneg_left (norm_nonneg a) hpos
      have h1 : |R| - |u.im| ≤ |R - u.im| := abs_sub_abs_le_abs_sub R u.im
      have h2 : |R| = R := abs_of_pos (lt_of_le_of_lt (abs_nonneg u.im) hR)
      have him : ((x : ℂ) + R * Complex.I - u).im = R - u.im := im_denom x R u
      calc R - |u.im| = |R| - |u.im| := by rw [h2]
        _ ≤ |R - u.im| := h1
        _ = |((x : ℂ) + R * Complex.I - u).im| := by rw [him]
        _ ≤ ‖(x : ℂ) + R * Complex.I - u‖ := Complex.abs_im_le_norm _
    exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
  · have htend : Filter.Tendsto (fun R : ℝ => R - |u.im|) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-|u.im|) Filter.tendsto_id
    have hdiv : Filter.Tendsto (fun R : ℝ => ‖a‖ / (R - |u.im|)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop htend
    simpa using hdiv.mul_const |q - p|

end Work.ZeroDensity.Ingham
