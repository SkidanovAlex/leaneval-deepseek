import Mathlib

namespace Work.ZeroFreeTables

open MeasureTheory

/-- For `0 ≤ b`, `0 ≤ z.re` and `h` continuous on `[0,b]`, the oscillating/decaying factor
`exp (-(z * t))` has modulus at most `1` on `[0,b]`, so the interval integral of
`exp (-(z * t)) * h t` is bounded in norm by the interval integral of `‖h t‖`. -/
theorem norm_intervalIntegral_exp_neg_mul_le (z : ℂ) (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 ≤ b)
    {h : ℝ → ℂ} (hcont : ContinuousOn h (Set.Icc (0:ℝ) b)) :
    ‖∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * h t‖ ≤ ∫ t in (0:ℝ)..b, ‖h t‖ := by
  have hexp_cont : Continuous (fun t : ℝ => Complex.exp (-(z * (t:ℂ)))) := by fun_prop
  have hFcont : ContinuousOn (fun t : ℝ => Complex.exp (-(z * (t:ℂ))) * h t)
      (Set.Icc (0:ℝ) b) :=
    (hexp_cont.continuousOn).mul hcont
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) b,
      ‖Complex.exp (-(z * (t:ℂ))) * h t‖ ≤ ‖h t‖ := by
    intro t ht
    rw [norm_mul]
    have hexp1 : ‖Complex.exp (-(z * (t:ℂ)))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      nlinarith [hz, ht.1]
    calc ‖Complex.exp (-(z * (t:ℂ)))‖ * ‖h t‖ ≤ 1 * ‖h t‖ := by gcongr
      _ = ‖h t‖ := one_mul _
  have hfc : IntervalIntegrable (fun t : ℝ => ‖Complex.exp (-(z * (t:ℂ))) * h t‖) volume 0 b :=
    (hFcont.norm).intervalIntegrable_of_Icc hb
  have hgc : IntervalIntegrable (fun t : ℝ => ‖h t‖) volume 0 b :=
    (hcont.norm).intervalIntegrable_of_Icc hb
  calc ‖∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * h t‖
      ≤ ∫ t in (0:ℝ)..b, ‖Complex.exp (-(z * (t:ℂ))) * h t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hb
    _ ≤ ∫ t in (0:ℝ)..b, ‖h t‖ :=
        intervalIntegral.integral_mono_on hb hfc hgc hbound

end Work.ZeroFreeTables
