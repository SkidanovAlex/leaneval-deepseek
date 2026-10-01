import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Analysis.Complex

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem integrable_laplace_vertical (c : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcpt : HasCompactSupport f) :
    MeasureTheory.Integrable (fun τ : ℝ =>
      ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t) := by
  set h : ℝ → ℂ := fun t => Complex.exp ((c : ℂ) * (t : ℂ)) * f t with hh
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := by
    rw [hh]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := by
      convert Complex.ofRealCLM.contDiff using 1
      ext t; simp [Complex.ofRealCLM_apply]
    exact (((contDiff_const.mul hlin)).cexp).mul hf
  have hcpt' : HasCompactSupport h := by
    rw [hh]; exact hcpt.mul_left
  have hFS : Integrable (𝓕 h) := by
    let S : SchwartzMap ℝ ℂ := hcpt'.toSchwartzMap hsm
    have h2 : Integrable (⇑(𝓕 S : SchwartzMap ℝ ℂ)) volume := (𝓕 S : SchwartzMap ℝ ℂ).integrable
    rw [SchwartzMap.fourier_coe] at h2
    exact h2
  set a : ℝ := -(2 * Real.pi)⁻¹ with ha
  have ha_ne : a ≠ 0 := by rw [ha]; exact neg_ne_zero.mpr (inv_ne_zero (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.pi)))
  have hcomp : Integrable (fun τ : ℝ => 𝓕 h (a * τ)) := hFS.comp_mul_left' ha_ne
  have hpt : (fun τ : ℝ => 𝓕 h (a * τ))
      = (fun τ : ℝ => ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t) := by
    funext τ
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with t
    simp only [Real.inner_apply, smul_eq_mul]
    rw [hh]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    have key : (↑(-2 * Real.pi * (t * (a * τ)) : ℝ) : ℂ) * Complex.I + (c : ℂ) * (t : ℂ)
        = ((c : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ) := by
      rw [ha]
      push_cast
      field_simp
      ring
    rw [key]
  rw [← hpt]
  exact hcomp

end Commons.Analysis.Complex
