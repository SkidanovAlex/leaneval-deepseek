import Mathlib
import Submission.Work.FIArea7.FourierDefs

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology FourierTransform

noncomputable section

/-- Pointwise convolution identity underlying the Fourier computation of the smooth trapezoid:
`sepK λ ε x = ε⁻¹ · ∫ t, boxK λ t · ρ((x - t)/ε)`, i.e. `sepK λ ε` is `ε⁻¹` times the
convolution of the interval indicator `boxK λ` with the dilated flat-topped density
`ρ(·/ε)`. -/
lemma sepK_eq_convolution_integral (lam eps : ℝ) (hε : 0 < eps) (hlam : 0 ≤ lam) (x : ℝ) :
    sepK lam eps x = (1/eps) * ∫ t, boxK lam t * sepRho ((x - t)/eps) := by
  have h1 : (∫ t : ℝ, boxK lam t * sepRho ((x - t)/eps))
      = ∫ t in (-lam)..lam, sepRho ((x - t)/eps) := by
    rw [show (fun t : ℝ => boxK lam t * sepRho ((x - t)/eps))
        = (Set.Icc (-lam) lam).indicator (fun t => sepRho ((x - t)/eps)) by
      funext t
      by_cases ht : t ∈ Set.Icc (-lam) lam
      · rw [Set.indicator_of_mem ht, show boxK lam t = 1 by simp [boxK, Set.indicator_of_mem ht],
          one_mul]
      · rw [Set.indicator_of_notMem ht, show boxK lam t = 0 by simp [boxK, Set.indicator_of_notMem ht],
          zero_mul]]
    rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  have h2 : (∫ t in (-lam)..lam, sepRho ((x - t)/eps))
      = ∫ t in (x-lam)..(x+lam), sepRho (t/eps) := by
    have h := intervalIntegral.integral_comp_sub_left (a := -lam) (b := lam)
      (fun u : ℝ => sepRho (u/eps)) x
    beta_reduce at h
    rw [h, show x - -lam = x + lam by ring]
  have h3 : (∫ t in (x-lam)..(x+lam), sepRho (t/eps)) = eps * sepK lam eps x := by
    rw [intervalIntegral.integral_comp_div sepRho hε.ne']
    rw [smul_eq_mul]
    have hsepK : sepK lam eps x = ∫ t in (x-lam)/eps..(x+lam)/eps, sepRho t := by
      have h := intervalIntegral.integral_interval_sub_left
        (sepRho_continuous.intervalIntegrable (μ := volume) (0:ℝ) ((x+lam)/eps))
        (sepRho_continuous.intervalIntegrable (μ := volume) (0:ℝ) ((x-lam)/eps))
      rw [← h]
      unfold sepK sepPsi
      rfl
    rw [hsepK]
  rw [h1, h2, h3]
  field_simp

/-- The Fourier transform of the interval indicator `boxK λ` (`λ > 0`, `t ≠ 0`):
`𝓕 boxK λ (t) = sin (2π λ t) / (π t)`. -/
lemma fourier_boxK_sin (lam : ℝ) (hlam : 0 < lam) (t : ℝ) (ht : t ≠ 0) :
    (FourierTransform.fourier (fun y : ℝ => (boxK lam y : ℂ)) t)
      = ((Real.sin (2 * Real.pi * lam * t) / (Real.pi * t) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I) • (boxK lam v : ℂ))
      = (Set.Icc (-lam) lam).indicator (fun v => Complex.exp (↑(-2*Real.pi*v*t) * Complex.I)) := by
    funext v
    rw [smul_eq_mul]
    by_cases hv : v ∈ Set.Icc (-lam) lam
    · rw [Set.indicator_of_mem hv, show boxK lam v = 1 by simp [boxK, Set.indicator_of_mem hv],
        Complex.ofReal_one, mul_one]
    · rw [Set.indicator_of_notMem hv, show boxK lam v = 0 by simp [boxK, Set.indicator_of_notMem hv],
        Complex.ofReal_zero, mul_zero]
  rw [hpt, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hc : (↑(-2 * Real.pi * t) * Complex.I : ℂ) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have h1' : (-2 * Real.pi * t : ℝ) = 0 := by exact_mod_cast h1
      have h2' : (-2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
      exact ht ((mul_eq_zero.mp (by simpa [mul_assoc] using h1')).resolve_left h2')
    · exact Complex.I_ne_zero h2
  simp_rw [show ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * t) * Complex.I)
      = Complex.exp ((↑(-2 * Real.pi * t) * Complex.I) * ↑v) by
    intro v; congr 1; push_cast; ring]
  rw [integral_exp_mul_complex hc]
  rw [show (↑(-2*Real.pi*t)*Complex.I * ↑lam : ℂ) = (↑(-(2*Real.pi*t*lam)))*Complex.I by push_cast; ring]
  rw [show (↑(-2*Real.pi*t)*Complex.I * ↑(-lam) : ℂ) = (↑(2*Real.pi*t*lam))*Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  rw [Real.cos_neg, Real.sin_neg]
  rw [show ((↑(Real.cos (2*Real.pi*t*lam)) + ↑(-Real.sin (2*Real.pi*t*lam)) * Complex.I)
      - (↑(Real.cos (2*Real.pi*t*lam)) + ↑(Real.sin (2*Real.pi*t*lam)) * Complex.I))
      = ↑(-2 * Real.sin (2*Real.pi*t*lam)) * Complex.I by push_cast; ring]
  rw [mul_div_mul_right _ _ Complex.I_ne_zero]
  rw [← Complex.ofReal_div]
  rw [Complex.ofReal_inj]
  rw [show (2*Real.pi*lam*t) = (2*Real.pi*t*lam) by ring]
  field_simp

/-- The real part of the Fourier transform of the dilated density `ρ(·/ε)` is `ε · cRho (ε t)`. -/
lemma fourier_sepRho_comp_re (eps : ℝ) (hε : 0 < eps) (t : ℝ) :
    (FourierTransform.fourier (fun y : ℝ => (sepRho (y/eps) : ℂ)) t).re
      = eps * cRho (eps * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hρ : Integrable (fun v : ℝ => (sepRho (v/eps) : ℂ)) := by
    have h := integrable_sepRho_comp (0:ℝ) eps hε
    simp only [add_zero] at h
    exact h.ofReal
  have hint : Integrable (fun v : ℝ =>
      Complex.exp (↑(-2*Real.pi*v*t)*Complex.I) • (sepRho (v/eps) : ℂ)) := by
    have hb : ∀ᵐ v : ℝ, ‖Complex.exp (↑(-2*Real.pi*v*t)*Complex.I)‖ ≤ 1 := by
      filter_upwards with v
      rw [Complex.norm_exp]
      simp
    have hm : AEStronglyMeasurable (fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*t)*Complex.I)) volume :=
      (by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2*Real.pi*v*t)*Complex.I)).aestronglyMeasurable
    refine (hρ.mul_bdd hm hb).congr ?_
    filter_upwards with v
    rw [smul_eq_mul, mul_comm]
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]
  simp only [Complex.reCLM_apply]
  have hre : ∀ v : ℝ, (Complex.exp (↑(-2*Real.pi*v*t)*Complex.I) • (sepRho (v/eps) : ℂ)).re
      = Real.cos (2*Real.pi*v*t) * sepRho (v/eps) := by
    intro v
    rw [smul_eq_mul, Complex.mul_re]
    rw [show (Complex.exp (↑(-2*Real.pi*v*t)*Complex.I)).re = Real.cos (-(2*Real.pi*v*t)) by
      rw [show (↑(-2*Real.pi*v*t) : ℂ) = ↑(-(2*Real.pi*v*t)) by push_cast; ring,
        Complex.exp_ofReal_mul_I_re]]
    rw [show (Complex.exp (↑(-2*Real.pi*v*t)*Complex.I)).im = Real.sin (-(2*Real.pi*v*t)) by
      rw [show (↑(-2*Real.pi*v*t) : ℂ) = ↑(-(2*Real.pi*v*t)) by push_cast; ring,
        Complex.exp_ofReal_mul_I_im]]
    rw [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.cos_neg]
  simp_rw [hre]
  have hpt : (fun v : ℝ => Real.cos (2*Real.pi*v*t) * sepRho (v/eps))
      = fun v => (fun u : ℝ => Real.cos (2*Real.pi*(eps*u)*t) * sepRho u) ((1/eps)*v) := by
    funext v
    simp only []
    rw [show eps*((1/eps)*v) = v by field_simp]
    rw [show (1/eps)*v = v/eps by ring]
  rw [hpt]
  have hcv := Measure.integral_comp_mul_left
    (fun u : ℝ => Real.cos (2*Real.pi*(eps*u)*t) * sepRho u) (1/eps)
  rw [hcv, show |(1/eps)⁻¹| = eps by simp only [one_div, inv_inv, abs_of_pos hε]]
  rw [smul_eq_mul]
  congr 1
  rw [cRho]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [show 2 * Real.pi * (eps * u) * t = 2 * Real.pi * u * (eps * t) by ring]

/-- The Fourier transform commutes with constant scalar multiplication (pointwise version,
avoiding the missing `FourierSMul` instance for bare functions). -/
lemma fourier_const_smul_pointwise (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    FourierTransform.fourier (c • f) t = c • FourierTransform.fourier f t := by
  simp only [Real.fourier_eq']
  simp_rw [Pi.smul_apply]
  rw [← MeasureTheory.integral_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [smul_comm]

/-- The Fourier transform of the smooth trapezoid `sepK lam eps`: for `t ≠ 0` its real part equals
`sin(2π·lam·t) · cRho (eps·t) / (π·t)`.

Proof route (the reviewer's): `sepK lam eps = boxK lam ⋆ (fun y => sepRho (y/eps))` pointwise
(`boxK lam` is the indicator of `[-lam,lam]`, given in `FourierDefs`), so Mathlib's
`Real.fourier_mul_convolution_eq` gives `𝓕 sepK = 𝓕 boxK * 𝓕(ρ(·/eps))`; the first factor is
`sin(2πλt)/(πt)` (interval integral of `exp (-2πiyt)`) and the real part of the second is
`eps * cRho (eps*t)` (change of variables `y = eps*u` and evenness of `sepRho`). -/
theorem SepKFourierIdent (lam eps : ℝ) (hε : 0 < eps) (hle : eps ≤ lam) (t : ℝ) (ht : t ≠ 0) :
    (FourierTransform.fourier (fun y : ℝ => (sepK lam eps y : ℂ)) t).re
      = Real.sin (2 * Real.pi * lam * t) * cRho (eps * t) / (Real.pi * t) := by
  have hlam : 0 < lam := lt_of_lt_of_le hε hle
  have hlam0 : 0 ≤ lam := le_of_lt hlam
  have hboxK_int : Integrable (boxK lam) := by
    rw [show boxK lam = (Set.Icc (-lam) lam).indicator (fun _ => (1:ℝ)) from rfl]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const (hs := (measure_Icc_lt_top).ne)
  have hF1 : Integrable (fun y : ℝ => (boxK lam y : ℂ)) := hboxK_int.ofReal
  have hF2 : Integrable (fun y : ℝ => (sepRho (y/eps) : ℂ)) := by
    have h := integrable_sepRho_comp (0:ℝ) eps hε
    simp only [add_zero] at h
    exact h.ofReal
  have hG : (fun y : ℝ => (sepK lam eps y : ℂ))
      = ((1/eps : ℝ) : ℂ) • MeasureTheory.convolution (fun y : ℝ => (boxK lam y : ℂ))
          (fun y : ℝ => (sepRho (y/eps) : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    have hcx : MeasureTheory.convolution (fun y : ℝ => (boxK lam y : ℂ))
        (fun y : ℝ => (sepRho (y/eps) : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) volume x
        = Complex.ofRealCLM (∫ s : ℝ, boxK lam s * sepRho ((x - s)/eps)) := by
      rw [MeasureTheory.convolution_def]
      rw [show (∫ s : ℝ, (ContinuousLinearMap.mul ℂ ℂ) ((boxK lam s : ℂ)) ((sepRho ((x - s)/eps) : ℂ)))
          = ∫ s : ℝ, ((boxK lam s * sepRho ((x - s)/eps) : ℝ) : ℂ) from by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with s
        simp only [ContinuousLinearMap.mul_apply', Complex.ofReal_mul]]
      exact integral_ofReal
    rw [Pi.smul_apply, hcx, sepK_eq_convolution_integral lam eps hε hlam0 x,
      Complex.ofReal_mul, smul_eq_mul]
    simp only [Complex.ofRealCLM_apply]
  rw [hG, fourier_const_smul_pointwise, Real.fourier_mul_convolution_eq hF1 hF2 t, smul_eq_mul]
  rw [fourier_boxK_sin lam hlam t ht, ← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, fourier_sepRho_comp_re eps hε t]
  field_simp

end

end Work.FIArea7
