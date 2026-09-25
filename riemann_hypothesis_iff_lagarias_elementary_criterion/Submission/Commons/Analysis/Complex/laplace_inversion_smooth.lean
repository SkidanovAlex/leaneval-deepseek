import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace Commons.Analysis.Complex

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem laplace_inversion_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcpt : HasCompactSupport f) (c u : ℝ) (hc : c ≠ 0) :
    f u = (1 / (2 * Real.pi)) * ∫ γ : ℝ,
      (∫ t : ℝ, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (t : ℂ))) * f t)
        * Complex.exp ((((c : ℂ) + γ * Complex.I)) * (u : ℂ)) := by
  have _ : c ≠ 0 := hc
  set h : ℝ → ℂ := fun t => Complex.exp (-(c : ℂ) * (t : ℂ)) * f t with hh
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := by
    rw [hh]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t:ℂ)) := by
      convert Complex.ofRealCLM.contDiff using 1
      ext t; simp [Complex.ofRealCLM_apply]
    exact (((contDiff_const.mul hlin)).cexp).mul hf
  have hcpt' : HasCompactSupport h := by
    rw [hh]; exact hcpt.mul_left
  have hS : Integrable h := (hcpt'.toSchwartzMap hsm).integrable (μ := volume)
  have hFS : Integrable (𝓕 h) := by
    let S : SchwartzMap ℝ ℂ := hcpt'.toSchwartzMap hsm
    have h2 : Integrable (⇑(𝓕 S : SchwartzMap ℝ ℂ)) volume := (𝓕 S : SchwartzMap ℝ ℂ).integrable
    rw [SchwartzMap.fourier_coe] at h2
    exact h2
  have hinv : 𝓕⁻ (𝓕 h) u = h u := congrFun (Continuous.fourierInv_fourier_eq hsm.continuous hS hFS) u
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h2πneR : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2πpos
  have h2πneC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2πneR
  have h2πneC' : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast h2πneR
  have hinner : ∀ γ : ℝ, (∫ t : ℝ, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (t : ℂ))) * f t)
      = 𝓕 h (γ / (2 * Real.pi)) := by
    intro γ
    have key : ∀ t : ℝ,
        (↑(-2 * Real.pi * (t * (γ / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I + (-(c:ℂ) * (t:ℂ))
          = -(((c:ℂ) + γ * Complex.I) * (t:ℂ)) := by
      intro t
      push_cast
      field_simp
      ring
    rw [hh, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with t
    simp only [Real.inner_apply, smul_eq_mul]
    calc Complex.exp (-((↑c + ↑γ * Complex.I) * ↑t)) * f t
        = Complex.exp ((↑(-2 * Real.pi * (t * (γ / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I + (-(↑c) * ↑t)) * f t := by rw [key t]
      _ = (Complex.exp ((↑(-2 * Real.pi * (t * (γ / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) * Complex.exp (-(↑c) * ↑t)) * f t := by
          rw [Complex.exp_add]
      _ = Complex.exp ((↑(-2 * Real.pi * (t * (γ / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) * (Complex.exp (-(↑c) * ↑t) * f t) := by
          rw [mul_assoc]
  have hsub : (∫ γ : ℝ, 𝓕 h (γ / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑γ * Complex.I) * (u : ℂ)))
      = ((2 * Real.pi : ℝ) : ℂ) * ∫ w : ℝ, (𝓕 h ((2 * Real.pi * w) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ))) := by
    have hA := Measure.integral_comp_mul_left
      (fun x : ℝ => 𝓕 h (x / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑x * Complex.I) * (u : ℂ)))
      (2 * Real.pi)
    rw [abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)] at hA
    have hA' : (∫ x : ℝ, 𝓕 h ((2 * Real.pi * x) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2 * Real.pi * x) * Complex.I) * (u : ℂ)))
        = (↑((2 * Real.pi)⁻¹) : ℂ) * (∫ y : ℝ, 𝓕 h (y / (2 * Real.pi)) *
            Complex.exp (((c : ℂ) + ↑y * Complex.I) * (u : ℂ))) := by
      simpa only [Complex.real_smul] using hA
    rw [hA', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2πneR, Complex.ofReal_one, one_mul]
  have hsub2 : (∫ w : ℝ, (𝓕 h ((2 * Real.pi * w) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ))))
      = ∫ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [mul_div_cancel_left₀ _ h2πneR]
  have hfac : ∀ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ))
      = Complex.exp ((c : ℂ) * (u : ℂ)) * (𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * u)) : ℝ) * Complex.I)) := by
    intro w
    have key : ((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ)
        = (c : ℂ) * (u : ℂ) + (↑(2 * Real.pi * (w * u)) : ℝ) * Complex.I := by
      push_cast
      ring
    rw [key, Complex.exp_add]
    ring
  have hIntFac : (∫ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2 * Real.pi * w) * Complex.I) * (u : ℂ)))
      = Complex.exp ((c : ℂ) * (u : ℂ)) *
        ∫ w : ℝ, 𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * u)) : ℝ) * Complex.I) := by
    simp_rw [hfac]
    rw [integral_const_mul]
  have hInv : (∫ w : ℝ, 𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * u)) : ℝ) * Complex.I))
      = 𝓕⁻ (𝓕 h) u := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with w
    simp only [Real.inner_apply, smul_eq_mul]
    ring
  have hLHS : (∫ γ : ℝ, (∫ t : ℝ, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (t : ℂ))) * f t)
        * Complex.exp (((c : ℂ) + γ * Complex.I) * (u : ℂ))) = ((2 * Real.pi : ℝ) : ℂ) * f u := by
    have e1 : (∫ γ : ℝ, (∫ t : ℝ, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (t : ℂ))) * f t)
        * Complex.exp (((c : ℂ) + γ * Complex.I) * (u : ℂ)))
        = ∫ γ : ℝ, 𝓕 h (γ / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑γ * Complex.I) * (u : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with γ
      rw [hinner γ]
    rw [e1, hsub, hsub2, hIntFac, hInv, hinv]
    have hh2 : h u = Complex.exp (-(c : ℂ) * (u : ℂ)) * f u := by rw [hh]
    rw [hh2]
    have : Complex.exp ((c : ℂ) * (u : ℂ)) * (Complex.exp (-(c : ℂ) * (u : ℂ)) * f u) = f u := by
      rw [← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]
    rw [this]
  rw [hLHS, one_div]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ h2πneC', one_mul]

end Commons.Analysis.Complex
