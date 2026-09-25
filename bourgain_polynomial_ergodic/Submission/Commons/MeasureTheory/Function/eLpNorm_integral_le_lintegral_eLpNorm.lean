import Mathlib
import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite

set_option linter.unusedVariables false

open MeasureTheory
open scoped ENNReal

namespace Commons.MeasureTheory.Function

theorem eLpNorm_integral_le_lintegral_eLpNorm
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SigmaFinite μ] [MeasureTheory.SigmaFinite ν]
    (f : α → β → E) (p : ℝ) (hp : 1 ≤ p)
    (hmeas : AEMeasurable (Function.uncurry f) (μ.prod ν))
    (hint : ∀ᵐ x ∂μ, MeasureTheory.Integrable (fun y => f x y) ν)
    (hFm : AEStronglyMeasurable (fun x => ∫ y, f x y ∂ν) μ) :
    MeasureTheory.eLpNorm (fun x => ∫ y, f x y ∂ν) (ENNReal.ofReal p) μ
      ≤ ∫⁻ y, MeasureTheory.eLpNorm (fun x => f x y) (ENNReal.ofReal p) μ ∂ν := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hstep1 : MeasureTheory.eLpNorm (fun x => ∫ y, f x y ∂ν) (ENNReal.ofReal p) μ
      ≤ MeasureTheory.eLpNorm (fun x => ∫⁻ y, ‖f x y‖ₑ ∂ν) (ENNReal.ofReal p) μ := by
    apply MeasureTheory.eLpNorm_mono_enorm hFm
    intro x
    simpa using enorm_integral_le_lintegral_enorm (fun y => f x y)
  have hmeas_swap : AEMeasurable (fun z : β × α => (Function.uncurry f) z.swap) (ν.prod μ) :=
    hmeas.prod_swap
  have hmeas_g : AEMeasurable (Function.uncurry (fun y x => ‖f x y‖ₑ)) (ν.prod μ) := by
    change AEMeasurable (fun z : β × α => ‖f z.2 z.1‖ₑ) (ν.prod μ)
    exact hmeas_swap.enorm
  have hstep2 := Commons.Analysis.Integral.lintegral_lintegral_le_lintegral_lintegral
    (μ := μ) (ν := ν) (p := ENNReal.ofReal p) hp'
    (g := fun y x => ‖f x y‖ₑ) hmeas_g
  have hcongr : (∫⁻ y, MeasureTheory.eLpNorm (fun x => ‖f x y‖ₑ) (ENNReal.ofReal p) μ ∂ν)
      ≤ ∫⁻ y, MeasureTheory.eLpNorm (fun x => f x y) (ENNReal.ofReal p) μ ∂ν := by
    refine lintegral_mono fun y => ?_
    by_cases hy : AEStronglyMeasurable (fun x => f x y) μ
    · exact le_of_eq (MeasureTheory.eLpNorm_enorm (fun x => f x y) hy)
    · rw [MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hy]
      exact le_top
  exact hstep1.trans (hstep2.trans hcongr)

end Commons.MeasureTheory.Function
