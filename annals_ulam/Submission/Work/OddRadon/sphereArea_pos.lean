import Mathlib
import Submission.Work.OddRadon.Core

namespace Work.OddRadon

open MeasureTheory

/-- The surface area of the unit sphere `S^m ⊆ ℝ^{m+1}` is positive.

`sphereArea m` is the total mass of `volume.toSphere`, the rotation-invariant
surface measure on the unit sphere of `EuclideanSpace ℝ (Fin (m+1))`.  Via
`Measure.toSphere_real_apply_univ` this is `(m+1) * volume.real (ball 0 1)`,
a product of two positive factors: the dimension `m+1` and the (real) volume of
the unit ball, which is positive because `volume` is `IsOpenPosMeasure` on the
finite-dimensional space `EuclideanSpace ℝ (Fin (m+1))`. -/
lemma sphereArea_pos (m : ℕ) : 0 < sphereArea m := by
  rw [sphereArea, MeasureTheory.Measure.toSphere_real_apply_univ]
  rw [finrank_euclideanSpace_fin]
  have h2 : 0 < (volume : Measure (EuclideanSpace ℝ (Fin (m+1)))).real (Metric.ball 0 1) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume 0 one_pos, measure_ball_lt_top⟩
  exact mul_pos (by exact_mod_cast Nat.succ_pos m) h2

end Work.OddRadon
