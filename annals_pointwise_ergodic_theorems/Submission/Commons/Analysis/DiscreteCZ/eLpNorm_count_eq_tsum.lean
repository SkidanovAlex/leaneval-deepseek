import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory

theorem eLpNorm_count_eq_tsum {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p)
    (u : ℤ → E) :
    MeasureTheory.eLpNorm u (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = (∑' x : ℤ, ‖u x‖ₑ ^ p) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le, MeasureTheory.lintegral_count]

end Commons.Analysis.DiscreteCZ