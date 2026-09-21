import Mathlib
import Submission.Work.OddRadon.Core

/-!
# Surface area of the circle: `sphereArea 1 = 2π`

`sphereArea m` (defined in `Submission.Work.OddRadon.Core`) is the total mass of the
rotation-invariant surface measure `Measure.toSphere volume` on the unit sphere
`S^m ⊆ ℝ^{m+1}`.  For `m = 1` the sphere is the unit circle in `ℝ²`, whose surface area is
`2π`.

The computation goes through Mathlib's `Measure.toSphere_real_apply_univ`, which identifies
the total mass of the surface measure with the *volume* of the unit ball in the ambient space
divided by the radius:

  `μ.toSphere.real Set.univ = μ.real (Metric.ball 0 1)`,

and then evaluates `volume (ball 0 1)` in `ℝ²` via
`EuclideanSpace.volume_ball_fin_two`, namely `π * r ^ 2`.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

lemma sphereArea_one : sphereArea 1 = 2 * Real.pi := by
  rw [sphereArea, MeasureTheory.Measure.toSphere_real_apply_univ]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_two]
  norm_num
  positivity

end Work.OddRadon
