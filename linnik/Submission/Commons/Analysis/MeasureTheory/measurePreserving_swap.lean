import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.MeasureTheory

/-! The coordinate swap `(x, y) ↦ (y, x)` on `ℝ × ℝ` preserves the product
Lebesgue measure `MeasureTheory.volume`.  -/
theorem measurePreserving_swap :
    MeasureTheory.MeasurePreserving (fun p : ℝ × ℝ => (p.2, p.1))
      MeasureTheory.volume MeasureTheory.volume := by
  -- the coordinate swap is `Prod.swap`, and `volume` on `ℝ × ℝ` is the
  -- product measure, which is invariant under swapping the two factors.
  change MeasureTheory.MeasurePreserving Prod.swap
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
  exact MeasureTheory.Measure.measurePreserving_swap
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))

end Commons.Analysis.MeasureTheory