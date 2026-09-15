import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory

namespace Commons.Measure.Real

/-- Reflection of a half-line integral: integrating over `(-∞, -c)` equals integrating `f (-·)`
over `(c, ∞)`. -/
theorem setIntegral_Iio_neg_eq_Ioi (f : ℝ → ℝ) (c : ℝ) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Iio (-c))) f
      = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi c)) (fun u => f (-u)) := by
  rw [← MeasureTheory.integral_Iic_eq_integral_Iio (f := f) (x := -c)]
  simpa only [neg_neg] using integral_comp_neg_Iic (-c) (fun y : ℝ => f (-y))

end Commons.Measure.Real