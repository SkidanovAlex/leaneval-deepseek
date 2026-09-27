import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory MeasureTheory.Measure

namespace Commons.Measure.RealEndgame

theorem measureReal_smul_image {c : ℝ} (hc : c ≠ 0) {s : Set ℝ} (hs : MeasurableSet s) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).real ((fun x : ℝ => c * x) ⁻¹' s) =
      |c⁻¹| * (MeasureTheory.volume : MeasureTheory.Measure ℝ).real s := by
  rw [← map_measureReal_apply (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun x : ℝ => c * x) (by fun_prop) hs]
  rw [Real.map_volume_mul_left hc]
  rw [measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]

end Commons.Measure.RealEndgame