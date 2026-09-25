import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

theorem aemeasurable_pairCount (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K) :
    AEMeasurable (fun a => pairCount K I R U a) volume := by
  -- `pairCount` is a finite sum over `u ∈ U` of countable sums over the lattice of products
  -- of two indicator functions of the window. Each such product is measurable since the
  -- window is measurable and translations are measurable, so the whole sum is measurable.
  unfold pairCount
  apply Measurable.aemeasurable
  apply Finset.measurable_sum
  intro u _
  unfold pairCountOne
  apply Measurable.tsum
  intro l
  apply Measurable.mul
  · exact ((measurable_const.indicator (measurableSet_window R))).comp (measurable_add_const _)
  · exact ((measurable_const.indicator (measurableSet_window R))).comp
      ((measurable_add_const _).add_const _)

end Work.Geometry
