import Mathlib

namespace Work.OddCurve.LowSlope

/-- For `p > -1`, the function `t ↦ (t - a) ^ p` is integrable on `(a, b)`. -/
theorem integrableOn_rpow_sub_left {a b p : ℝ} (hab : a < b) (hp : -1 < p) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t - a) ^ p) (Set.Ioo a b) MeasureTheory.volume := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
  have h1 : IntervalIntegrable (fun u : ℝ => u ^ p) MeasureTheory.volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have h2 := h1.comp_sub_right a
  simpa using h2

end Work.OddCurve.LowSlope
