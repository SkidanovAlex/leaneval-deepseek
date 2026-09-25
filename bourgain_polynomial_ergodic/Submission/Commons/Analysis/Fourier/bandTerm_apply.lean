import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped Interval

/-- The window integral of a band in closed form: substituting `θ = λ + h u` and using that `φ`
vanishes off `[-1,1]`,
`∫_{λ-h}^{λ+h} φ((θ-λ)/h) e^{-I z θ} dθ = h · (∫ u, φ u · e^{-I (h z) u}) · e^{-I λ z}`. -/
theorem bandTerm_apply (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h z : ℝ} (hh : 0 < h) :
    (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      = h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) := by
  -- the substitution `θ = λ + h u`
  have hsub : h * (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
        Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))))
      = (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ)))) := by
    rw [show (lam - h) = lam + h * (-1) by ring, show (lam + h) = lam + h * 1 by ring]
    rw [intervalIntegral.integral_comp_add_mul (f := fun th : ℝ => (φ ((th - lam) / h) : ℂ) *
      Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      (a := (-1 : ℝ)) (b := 1) (c := h) (d := lam) (ne_of_gt hh)]
    rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
      mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hh), one_mul]
  -- the pointwise identification of the integrand
  have hsimp : (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
        Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))))
      = ∫ u in (-1 : ℝ)..1, Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
        ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
    apply intervalIntegral.integral_congr
    intro u _
    show (φ ((lam + h * u - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
        ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
    have h1 : (lam + h * u - lam) / h = u := by field_simp; ring
    rw [show -(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ))
        = -(Complex.I * (lam : ℂ) * (z : ℂ)) + -(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)) by
      push_cast; ring, Complex.exp_add, h1]
    ring
  -- `φ` vanishes off `[-1,1]`, so the interval integral is a full-line integral
  have hzero : ∀ u : ℝ, u ∉ Set.Icc (-1 : ℝ) 1 →
      (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) = 0 := by
    intro u hu
    have h1 : 1 ≤ |u| := by
      rcases (not_and_or.mp hu) with h | h
      · rw [abs_of_neg (by linarith [not_le.mp h])]; linarith [not_le.mp h]
      · rw [abs_of_pos (by linarith [not_le.mp h])]; linarith [not_le.mp h]
    rw [hsupp u h1]; simp
  have hzero' : ∀ u : ℝ, u ∉ Set.Ioc (-1 : ℝ) 1 →
      (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) = 0 := by
    intro u hu
    by_cases h : u ∈ Set.Icc (-1 : ℝ) 1
    · have : u = -1 := by
        rw [Set.mem_Icc] at h; rw [Set.mem_Ioc] at hu
        have hle : u ≤ -1 := by
          by_contra hc
          exact hu ⟨not_le.mp hc, h.2⟩
        linarith [h.1]
      rw [this, hsupp (-1) (by norm_num)]; simp
    · exact hzero u h
  have hfull : (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))
      = ∫ u in (-1 : ℝ)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Ioc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_apply, if_neg hu]
      exact hzero' u hu
  calc (∫ th in (lam - h)..(lam + h),
        (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (th : ℂ))))
      = h * (∫ u in (-1 : ℝ)..1, (φ ((lam + h * u - lam) / h) : ℂ) *
          Complex.exp (-(Complex.I * (z : ℂ) * ((lam + h * u : ℝ) : ℂ)))) := hsub.symm
    _ = h * (∫ u in (-1 : ℝ)..1, Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ((φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ))))) := by
          rw [hsimp]
    _ = h * (Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ∫ u in (-1 : ℝ)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
          rw [intervalIntegral.integral_const_mul]
    _ = h * (Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) *
          ∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) := by
          rw [hfull]
    _ = h * (∫ u : ℝ, (φ u : ℂ) * Complex.exp (-(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)))) *
          Complex.exp (-(Complex.I * (lam : ℂ) * (z : ℂ))) := by ring

end Commons.Analysis.Fourier
/-!
Note: this lemma is the closed-form of the window integral (band term) used in the
circle-method decomposition of the polynomial ergodic averages.
-/
