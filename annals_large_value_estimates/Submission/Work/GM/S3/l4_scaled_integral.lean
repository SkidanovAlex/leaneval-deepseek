import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- Substitution `u = τ / T^η` in `∫ ψ(τ/T^η) e^{isτ} dτ`, identifying the result with the
Fourier transform of `ψ` at `-T^η s / (2π)` (Mathlib's normalisation `𝓕 f ξ = ∫ e(-ξx) f x`;
`MeasureTheory.integral_comp_mul_left` and `Real.fourier_real_eq_integral_exp_smul` do the work). -/
theorem l4_scaled_integral {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (s : ℝ) :
    (∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ))) =
      ((T ^ η : ℝ) : ℂ) * FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ))
        (-(T ^ η * s) / (2 * Real.pi)) := by
  -- `hψ`, `hcs`, `hη` are not needed: Mathlib's Fourier transform has no regularity hypotheses
  -- and the change of variables works for every (possibly non-integrable) function.
  have _ := hψ
  have _ := hcs
  have _ := hη
  have hcpos : 0 < T ^ η := Real.rpow_pos_of_pos hT η
  have hcne : T ^ η ≠ 0 := ne_of_gt hcpos
  -- Substitution `u = τ / T^η`, i.e. the change of variables `τ = T^η u`.
  have hcomp :
      (∫ x : ℝ,
          ((ψ (x / T ^ η) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((s * T ^ η * (x / T ^ η) : ℝ) : ℂ)))
        = ((T ^ η : ℝ) : ℂ) *
            ∫ y : ℝ,
              ((ψ y : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * T ^ η * y : ℝ) : ℂ)) := by
    have h := MeasureTheory.Measure.integral_comp_div
      (fun u : ℝ => ((ψ u : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * T ^ η * u : ℝ) : ℂ)))
      (T ^ η)
    rw [abs_of_pos hcpos, Complex.real_smul] at h
    exact h
  -- The integrand on the left is the substituted integrand.
  have hkey :
      (∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)))
        = ∫ x : ℝ,
            ((ψ (x / T ^ η) : ℝ) : ℂ) *
              Complex.exp (Complex.I * ((s * T ^ η * (x / T ^ η) : ℝ) : ℂ)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have h2 : T ^ η * (x / T ^ η) = x := by rw [mul_comm]; exact div_mul_cancel₀ x hcne
    have h1 : s * T ^ η * (x / T ^ η) = s * x := by rw [mul_assoc, h2]
    rw [h1]
  -- Match with Mathlib's Fourier transform normalisation.
  have hfou :
      (∫ v : ℝ,
          Complex.exp
              (((-2 * Real.pi * v * (-(T ^ η * s) / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) •
            ((ψ v : ℝ) : ℂ))
        = ∫ u : ℝ,
            ((ψ u : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * T ^ η * u : ℝ) : ℂ)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    have harg : (-2 * Real.pi * v * (-(T ^ η * s) / (2 * Real.pi))) = s * T ^ η * v := by
      field_simp
    rw [harg, smul_eq_mul, mul_comm (↑(s * T ^ η * v) : ℂ) Complex.I]
    exact mul_comm _ _
  rw [Real.fourier_real_eq_integral_exp_smul (fun x : ℝ => (ψ x : ℂ))
      (-(T ^ η * s) / (2 * Real.pi))]
  rw [hfou, hkey, hcomp]

end Work.GM.S3
