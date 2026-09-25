import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem aemeasurable_pointCount (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) :
    AEMeasurable (fun a => pointCount K I R a) volume := by
  -- the point count is a countable sum over the lattice of indicator functions, each of
  -- which is measurable since the window is measurable and translations are measurable
  unfold pointCount
  apply Measurable.aemeasurable
  apply Measurable.tsum
  intro l
  exact (Measurable.indicator measurable_const (measurableSet_window R)).comp
    (measurable_add_const _)

end Work.Geometry
