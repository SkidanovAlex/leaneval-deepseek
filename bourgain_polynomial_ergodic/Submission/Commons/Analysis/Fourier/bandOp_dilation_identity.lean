import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators ENNReal

/-- Dilation of the (space) variable in a Bochner integral over `ℝ`: rescaling the integration
variable by `σ > 0` multiplies the integral by `σ`.  This packages `Measure.integral_comp_div`. -/
lemma integral_eq_mul_integral_comp_mul (g : ℝ → ℂ) (σ : ℝ) (hσ : 0 < σ) :
    (∫ y : ℝ, g y) = (σ : ℂ) * ∫ Y : ℝ, g (σ * Y) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have h := Measure.integral_comp_div (fun t : ℝ => g (σ * t)) σ
  rw [show (∫ x : ℝ, g (σ * (x / σ))) = ∫ x : ℝ, g x from by
        apply integral_congr_ae
        filter_upwards with x
        rw [mul_div_cancel₀ x hσ']] at h
  rw [abs_of_pos hσ, Complex.real_smul] at h
  exact h

/-- Dilation of the *frequency* variable: substituting `ξ = σ θ` (`σ > 0`) in the Fourier-type
integral `∫ ξ, M (ξ/σ) · e^{-i (X-Y) ξ}` turns it into `σ · ∫ θ, M θ · e^{-i σ(X-Y) θ}`. -/
lemma bandOp_inner_identity (M : ℝ → ℂ) (σ X Y : ℝ) (hσ : 0 < σ) :
    (∫ ξ : ℝ, M (ξ / σ) * Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ))))
      = (σ : ℂ) *
          ∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * (θ : ℂ))) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  set g : ℝ → ℂ := fun t => M t * Complex.exp (-(Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * (t : ℂ))) with hg
  have harg : ∀ ξ : ℝ, Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ)
      = Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * ((ξ / σ : ℝ) : ℂ) := by
    intro ξ
    have hreal : (σ * X - σ * Y) * (ξ / σ) = (X - Y) * ξ := by field_simp
    calc Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ)
        = Complex.I * ((((X - Y) * ξ : ℝ) : ℂ)) := by rw [Complex.ofReal_mul]; ring
      _ = Complex.I * ((((σ * X - σ * Y) * (ξ / σ) : ℝ) : ℂ)) := by rw [hreal]
      _ = Complex.I * (((σ * X - σ * Y : ℝ) : ℂ)) * ((ξ / σ : ℝ) : ℂ) := by rw [Complex.ofReal_mul]; ring
  have hstep1 : (∫ ξ : ℝ, M (ξ / σ) * Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ))))
      = ∫ ξ : ℝ, g (ξ / σ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [hg]
    congr 2
    rw [harg ξ]
  rw [hstep1, Measure.integral_comp_div g σ, abs_of_pos hσ]
  rw [Complex.real_smul]

/-- **Dilation identity for the band-pass operator given as an iterated integral.**  For `σ > 0`
and any `M f : ℝ → ℂ`, dilating the frequency variable by `σ` is the same as dilating the space
variable by `σ`. -/
theorem bandOp_dilation_identity (M f : ℝ → ℂ) (σ X : ℝ) (hσ : 0 < σ) :
    (∫ y : ℝ, f (y / σ) *
        (∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (((σ * X - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = ∫ Y : ℝ, f Y *
          (∫ ξ : ℝ, M (ξ / σ) * Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ)))) := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  set I : ℝ → ℂ := fun z => ∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * ((z : ℝ) : ℂ) * (θ : ℂ))) with hI
  set J : ℝ → ℂ := fun Y => ∫ ξ : ℝ, M (ξ / σ) * Complex.exp (-(Complex.I * (((X - Y : ℝ) : ℂ)) * (ξ : ℂ))) with hJ
  have hJeq : ∀ Y : ℝ, J Y = (σ : ℂ) * I (σ * X - σ * Y) := by
    intro Y
    rw [hJ, hI]
    exact bandOp_inner_identity M σ X Y hσ
  have hLHS : (∫ y : ℝ, f (y / σ) * I (σ * X - y))
      = (σ : ℂ) * ∫ Y : ℝ, f Y * I (σ * X - σ * Y) := by
    have h := integral_eq_mul_integral_comp_mul (fun y : ℝ => f (y / σ) * I (σ * X - y)) σ hσ
    rw [h]
    congr 1
    apply integral_congr_ae
    filter_upwards with Y
    rw [mul_div_cancel_left₀ Y hσ']
  have hRHS : (∫ Y : ℝ, f Y * J Y) = (σ : ℂ) * ∫ Y : ℝ, f Y * I (σ * X - σ * Y) := by
    rw [show (∫ Y : ℝ, f Y * J Y) = ∫ Y : ℝ, f Y * ((σ : ℂ) * I (σ * X - σ * Y)) from by
          apply integral_congr_ae
          filter_upwards with Y
          rw [hJeq Y]]
    rw [show (∫ Y : ℝ, f Y * ((σ : ℂ) * I (σ * X - σ * Y)))
              = ∫ Y : ℝ, (σ : ℂ) * (f Y * I (σ * X - σ * Y)) from by
          apply integral_congr_ae
          filter_upwards with Y
          ring]
    rw [integral_const_mul]
  rw [show (∫ y : ℝ, f (y / σ) *
        (∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (((σ * X - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = (∫ y : ℝ, f (y / σ) * I (σ * X - y)) from rfl]
  rw [hLHS, ← hRHS]

end Commons.Analysis.Fourier