import Mathlib
import Submission.Work.Analysis.CzShift.Defs

/-!
# The Fourier transform of the shifted kernel `shiftKernelC`

For a scale `σ > 0` and a shift `t`, the shifted kernel
`shiftKernelC Ψ σ t x = σ⁻¹ Ψ((x - tσ)/σ)` is the convolution kernel of the Fourier
multiplier `ξ ↦ 𝓕Ψ(σξ) · e(-tσξ)`.  This module records exactly that computation: a
dilation (change of variables `x = σu` on the line) followed by a translation
(`Ψ(· - t)`), both at the level of the Lebesgue integral.

The main statement is `fourier_shiftKernelC`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory

set_option linter.unusedVariables false in
/-- Fourier transform of the shifted kernel `x ↦ σ⁻¹ Ψ((x - tσ)/σ)`: it equals the
Fourier transform of `Ψ` at the dilated frequency `σξ`, times the phase
`exp(-2πi tσξ)`.

The integrability hypothesis on `Ψ` is not needed for the computation (all the
change-of-variables lemmas used below are unconditional for the Bochner integral),
but it is the hypothesis under which the statement is used in the paper, and it is
what guarantees that both sides are the ordinary `L¹` Fourier integrals. -/
theorem fourier_shiftKernelC (Ψ : ℝ → ℂ) (σ t : ℝ) (hσ : 0 < σ)
    (hΨ : MeasureTheory.Integrable Ψ) :
    ∀ ξ : ℝ, FourierTransform.fourier (shiftKernelC Ψ σ t) ξ
      = FourierTransform.fourier Ψ (σ * ξ)
          * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t * σ * ξ : ℝ) : ℂ))) := by
  intro ξ
  -- Rewriting the integrand with the substitution `x = σ u`.
  have hG : (fun x : ℝ => Real.fourierChar (-(x * ξ)) • shiftKernelC Ψ σ t x)
      = fun x : ℝ =>
          Real.fourierChar (-((x / σ) * (σ * ξ))) • ((σ : ℂ)⁻¹ * Ψ (x / σ - t)) := by
    funext x
    simp only [shiftKernelC]
    have h1 : -((x / σ) * (σ * ξ)) = -(x * ξ) := by field_simp
    have h2 : (x - t * σ) / σ = x / σ - t := by field_simp
    rw [← h1, h2]
  -- The translation `u ↦ u - t` turns into the phase `e(-tσξ)`.
  have hT : Fourier.fourierIntegral Real.fourierChar volume (Ψ ∘ fun u => u + (-t)) (σ * ξ)
      = Real.fourierChar ((-t) * (σ * ξ)) •
          Fourier.fourierIntegral Real.fourierChar volume Ψ (σ * ξ) :=
    congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume Ψ (-t)) (σ * ξ)
  -- Both sides of `hT` are the usual Fourier integrals on `ℝ`.
  have hB : Fourier.fourierIntegral Real.fourierChar volume Ψ (σ * ξ)
      = FourierTransform.fourier Ψ (σ * ξ) := by
    rw [Real.fourier_real_eq, Fourier.fourierIntegral_def]
  -- Pulling the constant `σ⁻¹` out of the integral.
  have hInt : ∫ u : ℝ, Real.fourierChar (-(u * (σ * ξ))) • ((σ : ℂ)⁻¹ * Ψ (u - t))
      = (σ : ℂ)⁻¹ • Fourier.fourierIntegral Real.fourierChar volume
          (Ψ ∘ fun u => u + (-t)) (σ * ξ) := by
    rw [Fourier.fourierIntegral_def]
    conv_rhs => rw [← MeasureTheory.integral_smul ((σ : ℂ)⁻¹)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    simp only [Function.comp_apply, Circle.smul_def, smul_eq_mul]
    ring_nf
  calc FourierTransform.fourier (shiftKernelC Ψ σ t) ξ
      = ∫ x : ℝ, Real.fourierChar (-((x / σ) * (σ * ξ))) •
          ((σ : ℂ)⁻¹ * Ψ (x / σ - t)) := by
        rw [Real.fourier_real_eq, hG]
    _ = |σ| • ∫ u : ℝ, Real.fourierChar (-(u * (σ * ξ))) • ((σ : ℂ)⁻¹ * Ψ (u - t)) :=
        MeasureTheory.Measure.integral_comp_div
          (fun u : ℝ => Real.fourierChar (-(u * (σ * ξ))) • ((σ : ℂ)⁻¹ * Ψ (u - t))) σ
    _ = |σ| • ((σ : ℂ)⁻¹ • Fourier.fourierIntegral Real.fourierChar volume
          (Ψ ∘ fun u => u + (-t)) (σ * ξ)) := by
        rw [hInt]
    _ = |σ| • ((σ : ℂ)⁻¹ • (Real.fourierChar ((-t) * (σ * ξ)) •
          Fourier.fourierIntegral Real.fourierChar volume Ψ (σ * ξ))) := by
        rw [hT]
    _ = FourierTransform.fourier Ψ (σ * ξ) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t * σ * ξ : ℝ) : ℂ))) := by
        rw [hB]
        have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
        have hexp : (↑(Real.fourierChar ((-t) * (σ * ξ))) : ℂ)
            = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((t * σ * ξ : ℝ) : ℂ))) := by
          rw [Real.fourierChar_apply]
          congr 1
          push_cast
          ring
        simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul]
        rw [abs_of_pos hσ, hexp, ← mul_assoc, mul_inv_cancel₀ hσc, one_mul, mul_comm]

end Work.Analysis.CzShift
