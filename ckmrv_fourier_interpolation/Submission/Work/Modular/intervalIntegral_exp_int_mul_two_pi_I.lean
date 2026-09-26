import Mathlib

namespace Work.Modular

/-- For a nonzero integer `m`, the integral of `u ↦ exp (2π i m u)` over `[0,1]` vanishes:
the integrand is the derivative of `u ↦ exp (2π i m u) / (2π i m)` and
`exp (2π i m) = 1`. -/
theorem intervalIntegral_exp_int_mul_two_pi_I (m : ℤ) (hm : m ≠ 0) :
    ∫ u in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)) = 0 := by
  set c : ℂ := 2 * Real.pi * Complex.I * (m : ℂ) with hc
  have hc_ne : c ≠ 0 := by
    rw [hc]
    simp [hm]
  have hcexp : Complex.exp c = 1 := by
    rw [hc]
    rw [Complex.exp_eq_one_iff]
    exact ⟨m, by ring⟩
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => Complex.exp (c * (u:ℂ)) / c) (Complex.exp (c * (u:ℂ))) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => c * (u:ℂ)) (c * 1) u := HasDerivAt.const_mul c h1
    have h3 : HasDerivAt (fun u : ℝ => Complex.exp (c * (u:ℂ)))
        (Complex.exp (c * (u:ℂ)) * (c * 1)) u := h2.cexp
    have h4 := h3.div_const c
    have : Complex.exp (c * (u:ℂ)) * (c * 1) / c = Complex.exp (c * (u:ℂ)) := by
      rw [mul_one, mul_div_cancel_right₀ _ hc_ne]
    rwa [this] at h4
  have hint : IntervalIntegrable (fun u : ℝ => Complex.exp (c * (u:ℂ)))
      MeasureTheory.volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [hcexp]

end Work.Modular
