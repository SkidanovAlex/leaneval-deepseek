import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.Measure.Integral

open MeasureTheory
open scoped ENNReal

theorem integral_rpow_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ)
    (hfi : MeasureTheory.Integrable f μ) (hgi : MeasureTheory.Integrable g μ)
    (hprod : MeasureTheory.Integrable (fun a => f a ^ (1 - t) * g a ^ t) μ) :
    ∫ a, f a ^ (1 - t) * g a ^ t ∂μ ≤ (∫ a, f a ∂μ) ^ (1 - t) * (∫ a, g a ∂μ) ^ t := by
  have hp : 0 ≤ 1 - t := by linarith
  have hq : 0 ≤ t := ht0.le
  have hpq : (1 - t) + t = 1 := by ring
  -- a.e. nonnegativity of the product
  have hprod_nn : 0 ≤ᵐ[μ] fun a => f a ^ (1 - t) * g a ^ t :=
    (hf.and hg).mono fun a ha => mul_nonneg (Real.rpow_nonneg ha.1 _) (Real.rpow_nonneg ha.2 _)
  -- nonnegativity of the integrals
  have hIf_nn : 0 ≤ ∫ a, f a ∂μ := integral_nonneg_of_ae hf
  have hIg_nn : 0 ≤ ∫ a, g a ∂μ := integral_nonneg_of_ae hg
  have hR_nn : 0 ≤ (∫ a, f a ∂μ) ^ (1 - t) * (∫ a, g a ∂μ) ^ t :=
    mul_nonneg (Real.rpow_nonneg hIf_nn _) (Real.rpow_nonneg hIg_nn _)
  -- Hölder's inequality in the Lebesgue-integral form
  have hHolder := ENNReal.lintegral_mul_norm_pow_le hfm.ennreal_ofReal hgm.ennreal_ofReal hp hq hpq
  -- identify the left-hand side
  have hLHS : ∫⁻ a, ENNReal.ofReal (f a) ^ (1 - t) * ENNReal.ofReal (g a) ^ t ∂μ
      = ENNReal.ofReal (∫ a, f a ^ (1 - t) * g a ^ t ∂μ) := by
    have hae : (fun a => ENNReal.ofReal (f a) ^ (1 - t) * ENNReal.ofReal (g a) ^ t)
        =ᵐ[μ] (fun a => ENNReal.ofReal (f a ^ (1 - t) * g a ^ t)) := by
      filter_upwards [hf, hg] with a hfa hga
      rw [ENNReal.ofReal_rpow_of_nonneg hfa hp, ENNReal.ofReal_rpow_of_nonneg hga hq,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hfa (1 - t))]
    rw [lintegral_congr_ae hae, ofReal_integral_eq_lintegral_ofReal hprod hprod_nn]
  -- identify the right-hand side
  have hRHS : (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ^ (1 - t)
        * (∫⁻ a, ENNReal.ofReal (g a) ∂μ) ^ t
      = ENNReal.ofReal ((∫ a, f a ∂μ) ^ (1 - t) * (∫ a, g a ∂μ) ^ t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hf,
      ← ofReal_integral_eq_lintegral_ofReal hgi hg,
      ENNReal.ofReal_rpow_of_nonneg hIf_nn hp, ENNReal.ofReal_rpow_of_nonneg hIg_nn hq,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hIf_nn (1 - t))]
  have key : ENNReal.ofReal (∫ a, f a ^ (1 - t) * g a ^ t ∂μ)
      ≤ ENNReal.ofReal ((∫ a, f a ∂μ) ^ (1 - t) * (∫ a, g a ∂μ) ^ t) := by
    rw [← hLHS, ← hRHS]
    exact hHolder
  exact (ENNReal.ofReal_le_ofReal_iff hR_nn).mp key

end Commons.Measure.Integral