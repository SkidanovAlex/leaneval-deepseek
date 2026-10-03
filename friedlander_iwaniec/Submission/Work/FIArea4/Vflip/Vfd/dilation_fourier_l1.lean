import Mathlib

/-!
# `dilation_fourier_l1`

The `L¹` norm of the Fourier transform is invariant under dilations of the argument:

`∫ ξ, ‖𝓕 (fun x => g (c * x)) ξ‖ = ∫ ξ, ‖𝓕 g ξ‖` for every `c ≠ 0`.

This is the classical scaling identity for the Fourier transform,
`𝓕 (fun x => g (c * x)) ξ = |c|⁻¹ • 𝓕 g (ξ / c)`,
combined with the change of variables `ξ ↦ c⁻¹ • ξ` for the Lebesgue integral on `ℝ`.

Both the pointwise identity and the change of variables are stated with the convention that a
non-integrable function has integral zero, so no integrability hypothesis is needed.
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip.Vfd

noncomputable section

/-- The Fourier transform of a dilate `x ↦ g (c * x)`, as an integral against the character
`x ↦ e^{-2πi x ξ}`, is the integral of `y ↦ e^{-2πi y (ξ / c)} • g y` scaled by `|c|⁻¹`. -/
private lemma integral_character_comp_mul (g : ℝ → ℂ) (c η : ℝ) (hc : c ≠ 0) :
    (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * η)) * Complex.I) • g (c * y))
      = (|c|⁻¹ : ℝ) • 𝓕 g (c⁻¹ * η) := by
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  set φ : ℝ → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * (y * η)) * Complex.I) • g (c * y)
    with hφ
  -- change of variables `y ↦ c⁻¹ • y` for the Lebesgue integral
  have hcomp : (∫ y : ℝ, φ (c⁻¹ • y)) = |c| • (∫ y : ℝ, φ y) := by
    have h := Measure.integral_comp_inv_smul (μ := (volume : Measure ℝ)) φ c
    simpa using h
  -- the substituted integrand is the character of `𝓕 g (c⁻¹ * η)`
  have hφc : ∀ y : ℝ, φ (c⁻¹ • y)
      = Complex.exp (↑(-2 * Real.pi * (y * (c⁻¹ * η))) * Complex.I) • g y := by
    intro y
    simp only [hφ, smul_eq_mul]
    have hy : c * (c⁻¹ * y) = y := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    have harg : -2 * Real.pi * ((c⁻¹ * y) * η) = -2 * Real.pi * (y * (c⁻¹ * η)) := by ring
    rw [hy, harg]
  have hfourier : (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * (y * (c⁻¹ * η))) * Complex.I) • g y)
      = 𝓕 g (c⁻¹ * η) := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply]
  have h1 : (∫ y : ℝ, φ (c⁻¹ • y)) = 𝓕 g (c⁻¹ * η) := by
    simp_rw [hφc]
    exact hfourier
  have h2 : |c| • (∫ y : ℝ, φ y) = 𝓕 g (c⁻¹ * η) := by
    rw [← hcomp]; exact h1
  have h3 : (∫ y : ℝ, φ y) = (|c|⁻¹ : ℝ) • 𝓕 g (c⁻¹ * η) := by
    conv_rhs => rw [← h2]
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ habs, one_smul]
  simpa only [hφ] using h3

/-- Scaling identity for the Fourier transform of a dilation of the argument:
`𝓕 (fun x => g (c * x)) ξ = |c|⁻¹ • 𝓕 g (ξ / c)`. -/
lemma fourier_comp_mul (g : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) (ξ : ℝ) :
    𝓕 (fun x : ℝ => g (c * x)) ξ = (|c|⁻¹ : ℝ) • 𝓕 g (c⁻¹ * ξ) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  exact integral_character_comp_mul g c ξ hc

/-- The `L¹` norm of the Fourier transform is invariant under a dilation of the argument. -/
theorem dilation_fourier_l1 (g : ℝ → ℂ) (c : ℝ) (hc : c ≠ 0) :
    (∫ ξ : ℝ, ‖FourierTransform.fourier (fun x : ℝ => g (c * x)) ξ‖)
      = ∫ ξ : ℝ, ‖FourierTransform.fourier g ξ‖ := by
  have hscalepoint : ∀ ξ : ℝ, 𝓕 (fun x : ℝ => g (c * x)) ξ = (|c|⁻¹ : ℝ) • 𝓕 g (c⁻¹ * ξ) :=
    fun ξ => fourier_comp_mul g hc ξ
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  calc ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => g (c * x)) ξ‖
      = ∫ ξ : ℝ, ‖(|c|⁻¹ : ℝ) • 𝓕 g (c⁻¹ * ξ)‖ := by simp only [hscalepoint]
    _ = ∫ ξ : ℝ, |c|⁻¹ * ‖𝓕 g (c⁻¹ * ξ)‖ := by
          congr 1; ext ξ
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (abs_nonneg c))]
    _ = |c|⁻¹ * ∫ ξ : ℝ, ‖𝓕 g (c⁻¹ * ξ)‖ := by rw [integral_const_mul]
    _ = |c|⁻¹ * ∫ ξ : ℝ, ‖𝓕 g (c⁻¹ • ξ)‖ := rfl
    _ = |c|⁻¹ * (|c| • ∫ y : ℝ, ‖𝓕 g y‖) := by
          rw [Measure.integral_comp_inv_smul (volume : Measure ℝ) (fun y : ℝ => ‖𝓕 g y‖) c]
          simp only [Module.finrank_self, pow_one]
    _ = ∫ y : ℝ, ‖𝓕 g y‖ := by
          rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ habs, one_mul]

end

end Work.FIArea4.Vflip.Vfd
