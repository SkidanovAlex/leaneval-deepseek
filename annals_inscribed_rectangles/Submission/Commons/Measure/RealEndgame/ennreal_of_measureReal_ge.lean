import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Measure.RealEndgame

theorem ennreal_of_measureReal_ge {s : Set ℝ}
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ) s ≠ ⊤)
    (h : (1 / 3 : ℝ) ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ).real s) :
    ENNReal.ofReal (1 / 3) ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) s := by
  rw [MeasureTheory.measureReal_def] at h
  calc
    ENNReal.ofReal (1 / 3 : ℝ) ≤
        ENNReal.ofReal ((MeasureTheory.volume : MeasureTheory.Measure ℝ) s).toReal := by
      exact ENNReal.ofReal_le_ofReal h
    _ = (MeasureTheory.volume : MeasureTheory.Measure ℝ) s := by
      exact ENNReal.ofReal_toReal hfin

end Commons.Measure.RealEndgame