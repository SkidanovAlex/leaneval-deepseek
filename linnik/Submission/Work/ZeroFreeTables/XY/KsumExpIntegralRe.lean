import Mathlib

namespace Work.ZeroFreeTables.XY

theorem KsumExpIntegralRe (x₀ σ τ L : ℝ) (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) :
    (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))
          * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀,
          Real.cos (τ * L * t) * (Real.exp (-((σ - 1) * L * t)) * f t) := by
  -- Pointwise: the real part of the complex integrand is the real integrand.
  have hpt : ∀ t : ℝ,
      (Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))
          * ((f t : ℝ) : ℂ)).re
        = Real.cos (τ * L * t) * (Real.exp (-((σ - 1) * L * t)) * f t) := by
    intro t
    -- Expand the exponent as a real part plus a real multiple of `I`.
    have hc : -((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ))
        = ((-((σ - 1) * L * t) : ℝ) : ℂ) + ((-(τ * L * t) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hc, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Real.cos_neg]
    ring
  -- The integrand is continuous on the interval of integration.
  have hsub : Set.uIcc (0:ℝ) x₀ ⊆ Set.Ici 0 := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hx₀)] at ht
    exact ht.1
  have hfcont : Continuous
      (fun t : ℝ => Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul Complex.continuous_ofReal))
  have hfc : ContinuousOn (fun t : ℝ => ((f t : ℝ) : ℂ)) (Set.uIcc (0:ℝ) x₀) :=
    Complex.continuous_ofReal.comp_continuousOn (hcont.mono hsub)
  have hInt : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))
        * ((f t : ℝ) : ℂ)) MeasureTheory.volume (0:ℝ) x₀ :=
    (hfcont.continuousOn.mul hfc).intervalIntegrable
  -- Pull the real part through the interval integral.
  have hre : (∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))
          * ((f t : ℝ) : ℂ)).re
      = ∫ t in (0:ℝ)..x₀,
          (Complex.exp (-((((σ : ℂ) + (τ : ℂ) * Complex.I - 1) * L) * (t : ℂ)))
            * ((f t : ℝ) : ℂ)).re := by
    simpa only [Complex.reCLM_apply] using
      (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hInt).symm
  rw [hre]
  exact intervalIntegral.integral_congr (fun t _ => hpt t)

end Work.ZeroFreeTables.XY
