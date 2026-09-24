import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- Integrability of the scaled bump times a unimodular exponential (continuity + compact support
of the scaled function; note `T^η ≠ 0` since `T > 0`, `η > 0`). -/
theorem l4_scaled_integrable {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (s : ℝ) :
    MeasureTheory.Integrable (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ))) := by
  have _ := hη
  have hcne : T ^ η ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hT η)
  -- The scaled bump `τ ↦ ψ(τ / T^η)`, viewed in `ℂ`, is continuous …
  have hscaled_cont : Continuous fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hψ.comp (continuous_id.div_const _))
  -- … and compactly supported, since `τ ↦ τ / T^η = (T^η)⁻¹ • τ` is a homeomorphism of `ℝ`.
  have hreal_cs : HasCompactSupport fun τ : ℝ => ψ ((T ^ η)⁻¹ • τ) :=
    hcs.comp_smul (inv_ne_zero hcne)
  have hscaled_cs : HasCompactSupport fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) := by
    have h : (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ))
        = fun τ : ℝ => (Complex.ofReal ∘ fun τ : ℝ => ψ ((T ^ η)⁻¹ • τ)) τ := by
      funext τ
      simp only [Function.comp_apply, Complex.ofReal_inj]
      rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [h]
    exact hreal_cs.comp_left (by simp)
  -- Hence the scaled bump is integrable.
  have hint : MeasureTheory.Integrable (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ)) :=
    hscaled_cont.integrable_of_hasCompactSupport hscaled_cs
  -- The exponential factor is continuous and unimodular.
  have hexp_cont : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hcont : Continuous fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)) := hscaled_cont.mul hexp_cont
  -- Dominate the product by the (integrable) norm of the scaled bump.
  refine MeasureTheory.Integrable.mono'
    (f := fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((s * τ : ℝ) : ℂ)))
    (g := fun τ : ℝ => ‖((ψ (τ / T ^ η) : ℝ) : ℂ)‖)
    hint.norm hcont.aestronglyMeasurable ?_
  filter_upwards with τ
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

end Work.GM.S3
