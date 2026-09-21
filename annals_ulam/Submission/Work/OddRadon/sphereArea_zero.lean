import Mathlib
import Submission.Work.OddRadon.Core

/-!
# `sphereArea 0 = 2`

The `0`-dimensional unit sphere `S^0 = {±1} ⊆ ℝ` consists of two points, each of
surface measure `1`, so its total surface measure is `2`.  In the formalisation
`sphereArea m` is the total mass of the rotation-invariant surface measure
`Measure.toSphere volume` on `S^m ⊆ ℝ^{m+1}`, and for `m = 0` the ambient space
`ℝ^{0+1} = ℝ` is one-dimensional, so

`sphereArea 0 = finrank ℝ ℝ * volume.real (ball 0 1) = 1 * 2 = 2`.

The second factor is the Lebesgue measure of the unit interval, computed from
`EuclideanSpace.volume_ball` in dimension one.
-/

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- The Lebesgue measure of the unit ball of `ℝ^{1} = EuclideanSpace ℝ (Fin 1)` is `2`. -/
private lemma volume_real_ball_fin_one :
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = 2 := by
  rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball]
  -- `volume (ball 0 1) = ofReal 1 ^ 1 * ofReal (√π ^ 1 / Gamma (card ι / 2 + 1))`
  have hG : Real.Gamma ((1 : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  simp only [Fintype.card_fin, Nat.cast_one, pow_one, hG, ENNReal.ofReal_one, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp

lemma sphereArea_zero : sphereArea 0 = 2 := by
  rw [sphereArea, MeasureTheory.Measure.toSphere_real_apply_univ]
  -- `= (finrank ℝ (EuclideanSpace ℝ (Fin (0+1))) : ℝ) * volume.real (ball 0 1)`
  rw [finrank_euclideanSpace, Fintype.card_fin]
  norm_num
  exact volume_real_ball_fin_one

end Work.OddRadon
