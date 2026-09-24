import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform Real

/-- Integral over `ℝ` of an even function equals twice the integral over the positive half-line. -/
theorem integral_eq_two_mul_integral_Ioi_of_even {f : ℝ → ℝ} (hf : Function.Even f) :
    ∫ x, f x = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have h : ∀ x, f |x| = f x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · rw [abs_of_neg hx, hf x]
    · rw [abs_of_nonneg hx]
  have hcongr : ∫ x, f x = ∫ x, f |x| :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => (h x).symm))
  rw [hcongr, integral_comp_abs]

/-- Integral over `ℝ` of an odd function vanishes. -/
theorem integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Odd f) : ∫ x, f x = 0 := by
  have h1 : ∫ x, f (-x) = ∫ x, f x :=
    MeasurePreserving.integral_comp (Measure.measurePreserving_neg (volume : Measure ℝ))
      measurableEmbedding_neg f
  have h2 : ∫ x, f (-x) = - ∫ x, f x := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hf x))
  have h3 : ∫ x, f x = - ∫ x, f x := h1 ▸ h2
  have h4 : (∫ x, f x) + ∫ x, f x = 0 := neg_eq_iff_add_eq_zero.mp h3.symm
  have h5 : (2 : ℝ) • (∫ x, f x) = 0 := by rw [two_smul, h4]
  exact (smul_eq_zero.mp h5).resolve_left two_ne_zero

/-- For an even continuous compactly supported real function `g`, the Fourier transform of its
complexification is twice the half-line cosine integral. -/
theorem fourier_ofReal_eq_two_mul_integral_Ici_cos (g : ℝ → ℝ) (hg : Continuous g)
    (hc : HasCompactSupport g) (heven : ∀ t, g (-t) = g t) (ξ : ℝ) :
    FourierTransform.fourier (fun t => (g t : ℂ)) ξ
      = ((2 * ∫ t in Set.Ici (0:ℝ), g t * Real.cos (2 * Real.pi * ξ * t)) : ℂ) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hc
  have hi : Integrable (fun t : ℝ => (g t : ℂ)) := hgint.ofReal
  set F : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * (g v : ℂ)
    with hF_def
  have hFcont : Continuous F := by rw [hF_def]; fun_prop
  have hFint : Integrable F := by
    refine hi.mono hFcont.aestronglyMeasurable ?_
    filter_upwards with v
    rw [hF_def]
    simp only [Complex.norm_exp_ofReal_mul_I, norm_mul, one_mul, le_refl]
  have hfour : FourierTransform.fourier (fun t : ℝ => (g t : ℂ)) ξ = ∫ v, F v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hF_def]
  have hre : (∫ v, F v).re = ∫ v, (F v).re := (integral_re hFint).symm
  have him : (∫ v, F v).im = ∫ v, (F v).im := (integral_im hFint).symm
  have hre_pt : ∀ v, (F v).re = g v * Real.cos (2 * Real.pi * ξ * v) := by
    intro v
    rw [hF_def]
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [show (-2 * Real.pi * v * ξ) = -(2 * Real.pi * ξ * v) by ring, Real.cos_neg]
    ring
  have him_pt : ∀ v, (F v).im = Real.sin (-2 * Real.pi * v * ξ) * g v := by
    intro v
    rw [hF_def]
    simp only [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hevenψ : Function.Even (fun v : ℝ => g v * Real.cos (2 * Real.pi * ξ * v)) := by
    intro v
    show g (-v) * Real.cos (2 * Real.pi * ξ * (-v)) = g v * Real.cos (2 * Real.pi * ξ * v)
    rw [heven v]
    congr 1
    rw [show (2 * Real.pi * ξ * (-v)) = -(2 * Real.pi * ξ * v) by ring, Real.cos_neg]
  have hreval : (∫ v, F v).re
      = 2 * ∫ t in Set.Ici (0 : ℝ), g t * Real.cos (2 * Real.pi * ξ * t) := by
    rw [hre]
    rw [show (∫ v, (F v).re) = ∫ v, g v * Real.cos (2 * Real.pi * ξ * v) from
      integral_congr_ae (Filter.Eventually.of_forall hre_pt)]
    rw [integral_eq_two_mul_integral_Ioi_of_even hevenψ, integral_Ici_eq_integral_Ioi]
  have him_zero : (∫ v, F v).im = 0 := by
    rw [him]
    rw [show (∫ v, (F v).im) = ∫ v, Real.sin (-2 * Real.pi * v * ξ) * g v from
      integral_congr_ae (Filter.Eventually.of_forall him_pt)]
    apply integral_eq_zero_of_odd
    intro v
    show Real.sin (-2 * Real.pi * (-v) * ξ) * g (-v)
      = -(Real.sin (-2 * Real.pi * v * ξ) * g v)
    rw [heven v]
    rw [show (-2 * Real.pi * (-v) * ξ) = -(-2 * Real.pi * v * ξ) by ring, Real.sin_neg]
    ring
  rw [hfour]
  refine Complex.ext ?_ ?_
  · rw [hreval]; simp
  · rw [him_zero]; simp

end Commons.Analysis.Fourier