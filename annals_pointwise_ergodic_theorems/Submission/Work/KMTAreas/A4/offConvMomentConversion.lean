import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- Conversion of the two real Bochner integrals appearing in `Work.KMTAreas.A4.offConvMoment`
into their `ℝ≥0∞` (`∫⁻`) counterparts: the first moment of `v` and the `L¹` norm of the
derivative of a Schwartz function are both finite, and `ofReal` of an integral of a norm equals
the lintegral of the `enorm`. -/
theorem offConvMomentConversion (h v : SchwartzMap ℝ ℂ) :
    ENNReal.ofReal ((∫ y : ℝ, |y| * ‖v y‖) * ∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖)
      = (∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ) * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ := by
  -- Finiteness of the two real integrals and identification of each `ofReal` with its lintegral.
  have h1 : ENNReal.ofReal (∫ y : ℝ, |y| * ‖v y‖) = ∫⁻ y : ℝ, ‖y‖ₑ * ‖v y‖ₑ := by
    -- `y ↦ |y| * ‖v y‖` is integrable: it is `y ↦ ‖y‖ ^ 1 * ‖v y‖`, a Schwartz moment.
    have hvint : Integrable (fun y : ℝ => |y| * ‖v y‖) := by
      simpa [Real.norm_eq_abs] using v.integrable_pow_mul (volume) 1
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hvint
      (ae_of_all _ (fun y => by positivity))]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg y)]
  have h2 : ENNReal.ofReal (∫ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖) =
      ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ := by
    -- The derivative of a Schwartz function is again Schwartz, hence integrable.
    have hint : Integrable (fun x : ℝ => deriv (h : ℝ → ℂ) x) := by
      have hfun : (fun x : ℝ => deriv (h : ℝ → ℂ) x) =
          ⇑(SchwartzMap.derivCLM ℂ ℂ h) := by
        ext x; rw [SchwartzMap.derivCLM_apply]
      rw [hfun]
      exact (SchwartzMap.derivCLM ℂ ℂ h).integrable (μ := volume)
    exact MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hint
  rw [ENNReal.ofReal_mul (integral_nonneg (fun y => by positivity)), h1, h2]

end Work.KMTAreas.A4
