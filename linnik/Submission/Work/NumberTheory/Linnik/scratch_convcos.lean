import Mathlib

open MeasureTheory Real FourierTransform Filter
open scoped ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- The complexification of `g*g` is the convolution of the complexification of `g` with itself. -/
private lemma convolution_ofReal_self (g : ℝ → ℝ) (x : ℝ) :
    MeasureTheory.convolution (fun v : ℝ => (g v : ℂ)) (fun v : ℝ => (g v : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume x
      = ((∫ s : ℝ, g s * g (x - s) : ℝ) : ℂ) := by
  rw [MeasureTheory.convolution]
  change (∫ t : ℝ, (g t : ℂ) * (g (x - t) : ℂ)) = ↑(∫ s : ℝ, g s * g (x - s))
  rw [show (∫ t : ℝ, (g t : ℂ) * (g (x - t) : ℂ))
      = ∫ t : ℝ, ((g t * g (x - t) : ℝ) : ℂ) by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    push_cast
    ring]
  exact integral_ofReal

/-- **The cosine transform of a convolution square is a square.**

Let `g : ℝ → ℝ` be even and integrable. Then the cosine transform of `g*g` is the square of the
Fourier transform of `g`; in particular `∫ cos(yt)(g*g)(t) dt ≥ 0`.  This is the identity behind the
second half of Condition 2 for the extremal functions of Heath-Brown §7 (`ℜ F(it) ≥ 0`). -/
theorem convolution_cos_nonneg {g : ℝ → ℝ} (hg : Integrable g)
    (hgeven : ∀ v : ℝ, g (-v) = g v) (y : ℝ) :
    0 ≤ ∫ v : ℝ, Real.cos (y * v) * (∫ s : ℝ, g s * g (v - s)) := by
  set H : ℝ → ℝ := fun v => ∫ s : ℝ, g s * g (v - s) with hHdef
  set F : ℝ → ℂ := fun v => (g v : ℂ) with hFdef
  have hFi : Integrable F := hg.ofReal
  have hHi : Integrable H := by
    have h := hg.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg
    rw [hHdef]
    convert h using 1
    ext v
    rw [MeasureTheory.convolution]
    simp [hFdef]
  -- the Fourier transform identity
  have hfour : ∀ ξ : ℝ, 𝓕 F ξ = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with v
    rw [smul_eq_mul]
  have hmain : ∀ ξ : ℝ, (∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * ((H v : ℝ) : ℂ))
      = (𝓕 F ξ) * (𝓕 F ξ) := by
    intro ξ
    have hconv : 𝓕 (MeasureTheory.convolution F F (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume) ξ
        = (𝓕 F ξ) * (𝓕 F ξ) :=
      Real.fourier_bilin_convolution_eq (ContinuousLinearMap.mul ℂ ℂ) hFi hFi ξ
    rw [← hconv, Real.fourier_real_eq_integral_exp_smul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with v
    rw [smul_eq_mul, hHdef, convolution_ofReal_self g v]
  -- `𝓕 F ξ` is real, by evenness
  have hreal : ∀ ξ : ℝ, 𝓕 F ξ = starRingEnd ℂ (𝓕 F ξ) := by
    intro ξ
    have h1 : (∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v)
        = ∫ v : ℝ, Complex.exp (↑(-2 * π * (-v) * ξ) * Complex.I) * F (-v) :=
      (MeasureTheory.integral_neg_eq_self
        (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v) MeasureTheory.volume).symm
    have h2 : (∫ v : ℝ, Complex.exp (↑(-2 * π * (-v) * ξ) * Complex.I) * F (-v))
        = starRingEnd ℂ (∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v) := by
      rw [← integral_conj]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with v
      rw [hFdef]
      simp only [map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal, hgeven v]
      congr 1
      · congr 1
        push_cast
        ring
    calc 𝓕 F ξ = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v := hfour ξ
      _ = ∫ v : ℝ, Complex.exp (↑(-2 * π * (-v) * ξ) * Complex.I) * F (-v) := h1
      _ = starRingEnd ℂ (∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) * F v) := h2
      _ = starRingEnd ℂ (𝓕 F ξ) := by rw [hfour ξ]
  have him : (𝓕 F (y / (2 * π))).im = 0 := by
    have h := congrArg Complex.im (hreal (y / (2 * π)))
    simp only [Complex.conj_im] at h
    linarith
  -- integrability of the oscillatory integrand
  have hIint : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * (y / (2 * π))) * Complex.I)
      * ((H v : ℝ) : ℂ)) := by
    refine hHi.norm.mono' ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop : Continuous fun v : ℝ => ↑(-2 * π * v * (y / (2 * π))) * Complex.I)).aestronglyMeasurable.mul
        hHi.ofReal.aestronglyMeasurable
    · filter_upwards with v
      rw [norm_mul, Complex.norm_exp]
      have h1 : ((↑(-2 * π * v * (y / (2 * π))) : ℂ) * Complex.I).re = 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [h1, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hstep : (∫ v : ℝ, Real.cos (y * v) * H v)
      = (𝓕 F (y / (2 * π))).re * (𝓕 F (y / (2 * π))).re := by
    have hpt : ∀ v : ℝ, (Complex.exp (↑(-2 * π * v * (y / (2 * π))) * Complex.I)
        * ((H v : ℝ) : ℂ)).re = Real.cos (y * v) * H v := by
      intro v
      have harg : (-2 * π * v * (y / (2 * π)) : ℝ) = -(y * v) := by
        field_simp
      rw [harg]
      have hzre : (↑(-(y * v)) * Complex.I).re = 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have hzim : (↑(-(y * v)) * Complex.I).im = -(y * v) := by
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, hzre, hzim]
      simp only [Real.exp_zero, one_mul, Real.cos_neg, Real.sin_neg, zero_mul, sub_zero,
        zero_sub, neg_mul, neg_neg, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        neg_zero]
    have h2 : (∫ v : ℝ, (Complex.exp (↑(-2 * π * v * (y / (2 * π))) * Complex.I)
        * ((H v : ℝ) : ℂ)).re) = (𝓕 F (y / (2 * π))).re * (𝓕 F (y / (2 * π))).re := by
      rw [show (∫ v : ℝ, (Complex.exp (↑(-2 * π * v * (y / (2 * π))) * Complex.I)
            * ((H v : ℝ) : ℂ)).re)
          = ((∫ v : ℝ, Complex.exp (↑(-2 * π * v * (y / (2 * π))) * Complex.I)
            * ((H v : ℝ) : ℂ))).re from integral_re hIint]
      rw [hmain (y / (2 * π)), Complex.mul_re, him]
      ring
    rw [← h2, MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)]
  rw [hstep]
  exact mul_self_nonneg _

end Commons.NumberTheory.Linnik
