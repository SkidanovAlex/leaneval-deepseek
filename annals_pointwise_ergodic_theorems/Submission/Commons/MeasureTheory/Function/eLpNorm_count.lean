import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

open scoped ENNReal

namespace Commons.MeasureTheory.Function

theorem eLpNorm_count {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (f : α → ℂ) :
    MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      = (∑' x, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
      MeasureTheory.AEStronglyMeasurable.of_discrete,
    MeasureTheory.lintegral_count]

end Commons.MeasureTheory.Function