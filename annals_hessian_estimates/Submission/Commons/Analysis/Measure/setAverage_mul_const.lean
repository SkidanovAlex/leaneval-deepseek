import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
theorem setAverage_mul_const {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))} (c : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (⨍ x in s, c * f x) = c * ⨍ x in s, f x := by
  rw [setAverage_eq, setAverage_eq, integral_const_mul]
  ring

end Commons.Analysis.Measure