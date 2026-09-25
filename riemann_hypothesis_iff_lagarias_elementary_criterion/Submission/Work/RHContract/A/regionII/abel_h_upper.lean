import Mathlib

open MeasureTheory

namespace Work.RHContract.A.regionII

/-- Upper bound for the Abel-type integral `∫_a^b (2 log t + 1)/(t³ log²t) dt`.

Since `t ↦ log t` is increasing and positive on `[a,b]` (with `a > 1`), for every
`t ∈ [a,b]` we have

`(2 log t + 1)/(t³ log²t) = ((2 log t + 1)/log²t)/t³ ≤ C/t³`,

where `C = (2 + 1/log a)/log a`.  Integrating the bound `C/t³` (whose primitive is
`-(C/2)/t²`) over `[a,b]` gives the stated right-hand side. -/
theorem abel_h_upper {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (2 * Real.log t + 1)/(t^3 * (Real.log t)^2)
      ≤ ((2 + 1/Real.log a)/Real.log a)/2 * (1/a^2 - 1/b^2) := by
  set C : ℝ := (2 + 1/Real.log a)/Real.log a with hC
  have hla : 0 < Real.log a := Real.log_pos ha
  have ha0 : 0 < a := lt_trans one_pos ha
  have hbpos : 0 < b := lt_of_lt_of_le ha0 hab
  have hCa : C = (2*Real.log a + 1)/(Real.log a)^2 := by
    rw [hC]; field_simp
  -- Pointwise comparison of the integrand with `C/t³` on `[a,b]`.
  have hbound : ∀ x ∈ Set.Icc a b,
      (2 * Real.log x + 1)/(x^3 * (Real.log x)^2) ≤ C/x^3 := by
    intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
    have hxpos : 0 < x := lt_trans one_pos hx1
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hlx_ge : Real.log a ≤ Real.log x := Real.log_le_log ha0 hx.1
    have hkey' : (2 * Real.log x + 1)/(Real.log x)^2 ≤ (2*Real.log a + 1)/(Real.log a)^2 := by
      have hnum : 0 ≤ (2*Real.log a+1)*(Real.log x)^2 - (2*Real.log x+1)*(Real.log a)^2 := by
        have hfac : (2*Real.log a+1)*(Real.log x)^2 - (2*Real.log x+1)*(Real.log a)^2
            = (Real.log x - Real.log a)*(2*Real.log a*Real.log x + Real.log x + Real.log a) := by ring
        rw [hfac]
        exact mul_nonneg (sub_nonneg.mpr hlx_ge) (by positivity)
      have hden : 0 < (Real.log a)^2 * (Real.log x)^2 := by positivity
      have heq : (2*Real.log a+1)/(Real.log a)^2 - (2*Real.log x+1)/(Real.log x)^2
          = ((2*Real.log a+1)*(Real.log x)^2 - (2*Real.log x+1)*(Real.log a)^2)/((Real.log a)^2*(Real.log x)^2) := by
        field_simp
      have : 0 ≤ (2*Real.log a+1)/(Real.log a)^2 - (2*Real.log x+1)/(Real.log x)^2 := by
        rw [heq]; exact div_nonneg hnum hden.le
      linarith
    have hkey : (2 * Real.log x + 1)/(Real.log x)^2 ≤ C := by
      rw [hCa]; exact hkey'
    rw [show (2 * Real.log x + 1)/(x^3 * (Real.log x)^2)
        = ((2 * Real.log x + 1)/(Real.log x)^2)/x^3 from by rw [div_div]; ring]
    exact div_le_div_of_nonneg_right hkey (by positivity)
  -- Integrability of both sides on `[a,b]`.
  have hf_cont : ContinuousOn (fun x : ℝ => (2*Real.log x+1)/(x^3*(Real.log x)^2)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hlog : ContinuousOn (fun x : ℝ => Real.log x) (Set.Icc a b) :=
      ContinuousOn.log continuous_id.continuousOn (fun x hx =>
        ne_of_gt (lt_trans one_pos (lt_of_lt_of_le ha hx.1)))
    have hnum : ContinuousOn (fun x : ℝ => 2*Real.log x + 1) (Set.Icc a b) :=
      (continuousOn_const.mul hlog).add continuousOn_const
    have hden : ContinuousOn (fun x : ℝ => x^3 * (Real.log x)^2) (Set.Icc a b) :=
      (continuous_id.continuousOn.pow 3).mul (hlog.pow 2)
    exact hnum.div hden (fun x hx =>
      ne_of_gt (by
        have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
        have hxpos : 0 < x := lt_trans one_pos hx1
        have hlx : 0 < Real.log x := Real.log_pos hx1
        positivity))
  have hf_int : IntervalIntegrable (fun x : ℝ => (2*Real.log x+1)/(x^3*(Real.log x)^2)) volume a b :=
    hf_cont.intervalIntegrable
  have hg_cont : ContinuousOn (fun x : ℝ => C/x^3) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (continuous_id.continuousOn.pow 3) (fun x hx =>
      ne_of_gt (by
        have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
        have hxpos : 0 < x := lt_trans one_pos hx1
        positivity))
  have hg_int : IntervalIntegrable (fun x : ℝ => C/x^3) volume a b :=
    hg_cont.intervalIntegrable
  have hmono : (∫ x in a..b, (2*Real.log x+1)/(x^3*(Real.log x)^2)) ≤ ∫ x in a..b, C/x^3 :=
    intervalIntegral.integral_mono_on hab hf_int hg_int hbound
  -- Fundamental theorem of calculus for `C/t³`, whose primitive is `-(C/2)/t²`.
  have hF_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => -(C/2)/t^2) (C/x^3) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : 1 < x := lt_of_lt_of_le ha hx.1
    have hxpos : 0 < x := lt_trans one_pos hx1
    have hx2 : x^2 ≠ 0 := ne_of_gt (by positivity)
    have hraw : HasDerivAt (fun t : ℝ => -(C/2)/t^2) ((0 * x^2 - (-(C/2))*(↑(2:ℕ)*x^(2-1)))/(x^2)^2) x :=
      (hasDerivAt_const x (-(C/2))).div (hasDerivAt_pow 2 x) hx2
    have hval : (0 * x^2 - (-(C/2))*(↑(2:ℕ)*x^(2-1)))/(x^2)^2 = C/x^3 := by
      have hxne : x ≠ 0 := ne_of_gt hxpos
      field_simp; ring
    rw [hval] at hraw
    exact hraw
  have hFTC : (∫ x in a..b, C/x^3) = (fun t : ℝ => -(C/2)/t^2) b - (fun t : ℝ => -(C/2)/t^2) a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv hg_int
  have hval2 : (fun t : ℝ => -(C/2)/t^2) b - (fun t : ℝ => -(C/2)/t^2) a
      = C/2 * (1/a^2 - 1/b^2) := by
    have ha2 : a ≠ 0 := ne_of_gt ha0
    have hb2 : b ≠ 0 := ne_of_gt hbpos
    simp only []
    field_simp
    ring
  calc (∫ t in a..b, (2 * Real.log t + 1)/(t^3 * (Real.log t)^2))
      ≤ ∫ x in a..b, C/x^3 := hmono
    _ = C/2 * (1/a^2 - 1/b^2) := by rw [hFTC, hval2]
    _ = ((2 + 1/Real.log a)/Real.log a)/2 * (1/a^2 - 1/b^2) := by rw [hC]

end Work.RHContract.A.regionII
