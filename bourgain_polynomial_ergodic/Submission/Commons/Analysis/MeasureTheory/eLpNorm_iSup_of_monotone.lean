import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq

open MeasureTheory

namespace Commons.Analysis.MeasureTheory

theorem eLpNorm_iSup_of_monotone {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) {u : ℕ → α → ENNReal}
    (hu : ∀ n, Measurable (u n)) (hmono : Monotone u) :
    MeasureTheory.eLpNorm (fun x => ⨆ n, u n x) p μ
      = ⨆ n, MeasureTheory.eLpNorm (u n) p μ := by
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hInt : ∫⁻ x, ‖(⨆ n, u n x)‖ₑ ^ p.toReal ∂μ
      = ⨆ n, ∫⁻ x, ‖u n x‖ₑ ^ p.toReal ∂μ := by
    have hcongr : (fun x => ‖(⨆ n, u n x)‖ₑ ^ p.toReal)
        = fun x => ⨆ n, ‖u n x‖ₑ ^ p.toReal := by
      funext x
      simp only [enorm_eq_self]
      exact iSup_rpow_eq hq_pos _
    rw [hcongr]
    refine lintegral_iSup ?_ ?_
    · intro n
      exact ENNReal.continuous_rpow_const.measurable.comp (hu n)
    · intro n m hnm x
      exact ENNReal.rpow_le_rpow (by simpa only [enorm_eq_self] using hmono hnm x) hq_pos.le
  calc MeasureTheory.eLpNorm (fun x => ⨆ n, u n x) p μ
      = (∫⁻ x, ‖(⨆ n, u n x)‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
          (Measurable.iSup hu).aestronglyMeasurable
    _ = (⨆ n, ∫⁻ x, ‖u n x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by rw [hInt]
    _ = ⨆ n, (∫⁻ x, ‖u n x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        iSup_rpow_eq (one_div_pos.mpr hq_pos) _
    _ = ⨆ n, MeasureTheory.eLpNorm (u n) p μ := by
        refine iSup_congr fun n => ?_
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (hu n).aestronglyMeasurable]

end Commons.Analysis.MeasureTheory
