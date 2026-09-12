import Mathlib
import Submission.Commons.Analysis.Potential.log_kernel_polarization

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory

/-- Tonelli plus an a.e. potential identity against a probability measure: the iterated
integral of the log kernel collapses to the constant `ofReal (log D)`. -/
private lemma prod_lintegral_eq_of_potential {μ ν : MeasureTheory.Measure ℂ}
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] {D : ℝ}
    (h : ∀ᵐ x ∂μ,
      ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂ν = ENNReal.ofReal (Real.log D)) :
    ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖)) ∂(μ.prod ν)
      = ENNReal.ofReal (Real.log D) := by
  have hk : Measurable (fun z : ℂ × ℂ => ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖))) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.measurable_log.comp ?_
    exact measurable_const.div ((measurable_fst.sub measurable_snd).norm)
  rw [MeasureTheory.lintegral_prod _ hk.aemeasurable]
  have hae : (fun x : ℂ => ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖(x, y).1 - (x, y).2‖)) ∂ν)
      =ᵐ[μ] fun _ => ENNReal.ofReal (Real.log D) := by
    filter_upwards [h] with x hx
    simpa using hx
  rw [MeasureTheory.lintegral_congr_ae hae, MeasureTheory.lintegral_const,
    MeasureTheory.measure_univ, mul_one]

theorem log_kernel_lintegral_ge_of_potential_eq {K : Set ℂ} (hK : IsCompact K)
    {D : ℝ} (hD : 0 < D) (hDiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (μ μ₀ : MeasureTheory.Measure ℂ) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure μ₀] [MeasureTheory.NullSingletonClass μ]
    [MeasureTheory.NullSingletonClass μ₀]
    (hμK : μ Kᶜ = 0) (hμ₀K : μ₀ Kᶜ = 0)
    (hpot : ∀ᵐ x ∂μ,
      ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂μ₀ = ENNReal.ofReal (Real.log D))
    (hpot₀ : ∀ᵐ x ∂μ₀,
      ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂μ₀ = ENNReal.ofReal (Real.log D)) :
    ENNReal.ofReal (Real.log D)
      ≤ ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖)) ∂(μ.prod μ) := by
  have hKm : ∀ᵐ x ∂μ, x ∈ K := by
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hμK
    filter_upwards [hμK] with x hx
    simpa using hx
  have hKm₀ : ∀ᵐ x ∂μ₀, x ∈ K := by
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hμ₀K
    filter_upwards [hμ₀K] with x hx
    simpa using hx
  have hμ_diam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖x - y‖ ≤ D := by
    filter_upwards [hKm] with x hx
    filter_upwards [hKm] with y hy
    exact hDiam x hx y hy
  have hμ₀_diam : ∀ᵐ x ∂μ₀, ∀ᵐ y ∂μ₀, ‖x - y‖ ≤ D := by
    filter_upwards [hKm₀] with x hx
    filter_upwards [hKm₀] with y hy
    exact hDiam x hx y hy
  have hμμ₀_diam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ₀, ‖x - y‖ ≤ D := by
    filter_upwards [hKm] with x hx
    filter_upwards [hKm₀] with y hy
    exact hDiam x hx y hy
  have hB : ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖)) ∂(μ.prod μ₀)
      = ENNReal.ofReal (Real.log D) := prod_lintegral_eq_of_potential hpot
  have hC : ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖)) ∂(μ₀.prod μ₀)
      = ENNReal.ofReal (Real.log D) := prod_lintegral_eq_of_potential hpot₀
  have hpol := Commons.Analysis.Potential.log_kernel_polarization μ μ₀ hD
    hμ_diam hμ₀_diam hμμ₀_diam
  rw [hB, hC, two_mul] at hpol
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hpol

end Commons.MeasureTheory
