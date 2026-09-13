import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace Commons.Measure.EuclideanSpace

open MeasureTheory MeasureTheory.Measure Metric ENNReal

/-- The ratio of the Lebesgue volumes of two balls in `EuclideanSpace ℝ (Fin n)` is `(s/r)^n`. -/
theorem volume_ball_ratio {n : ℕ} {x₀ y : EuclideanSpace ℝ (Fin n)} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    (MeasureTheory.volume (Metric.ball y s)).toReal
      / (MeasureTheory.volume (Metric.ball x₀ r)).toReal = (s / r) ^ n := by
  have hvol : ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      MeasureTheory.volume (Metric.ball x t)
        = ENNReal.ofReal (t ^ n) * MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro x t ht
    have h := addHaar_ball_mul_of_pos MeasureTheory.volume x ht 1
    rw [mul_one] at h
    rw [h, finrank_euclideanSpace, Fintype.card_fin]
  have hnum : (MeasureTheory.volume (Metric.ball y s)).toReal
      = s ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [hvol y s hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le n)]
  have hden : (MeasureTheory.volume (Metric.ball x₀ r)).toReal
      = r ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [hvol x₀ r hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  have hVne : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal ≠ 0 := by
    apply ne_of_gt
    rw [ENNReal.toReal_pos_iff]
    refine ⟨Metric.measure_ball_pos MeasureTheory.volume (0 : EuclideanSpace ℝ (Fin n)) one_pos, ?_⟩
    exact lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).measure_lt_top)
  rw [hnum, hden, mul_div_mul_right (s ^ n) (r ^ n) hVne, ← div_pow]

end Commons.Measure.EuclideanSpace