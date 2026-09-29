import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace Commons.Measure.EuclideanSpace

open MeasureTheory MeasureTheory.Measure Metric ENNReal

/-- The Lebesgue volume of the unit ball in `EuclideanSpace ℝ (Fin (n+2))` is `2π/(n+2)` times
the volume of the unit ball in `EuclideanSpace ℝ (Fin n)`. -/
theorem volume_ball_add_two (n : ℕ) (hn : 1 ≤ n) :
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)).toReal
      = 2 * Real.pi / ((n : ℝ) + 2)
          * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
      = ENNReal.ofReal (Real.sqrt Real.pi ^ (n + 2)
          / Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1)) := by
    rw [EuclideanSpace.volume_ball]
    simp [Fintype.card_fin]
  have h2 : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      = ENNReal.ofReal (Real.sqrt Real.pi ^ n
          / Real.Gamma ((n : ℝ) / 2 + 1)) := by
    rw [EuclideanSpace.volume_ball]
    simp [Fintype.card_fin]
  rw [h1, h2, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · have hG : Real.Gamma (((n + 2 : ℕ) : ℝ) / 2 + 1)
        = ((n : ℝ) / 2 + 1) * Real.Gamma ((n : ℝ) / 2 + 1) := by
      have harg : (((n + 2 : ℕ) : ℝ) / 2 + 1) = ((n : ℝ) / 2 + 1) + 1 := by
        push_cast; ring
      rw [harg, Real.Gamma_add_one (by positivity)]
    rw [hG]
    have hpow : Real.sqrt Real.pi ^ (n + 2) = Real.sqrt Real.pi ^ n * Real.pi := by
      rw [pow_add, Real.sq_sqrt Real.pi_nonneg]
    rw [hpow]
    rw [show (2:ℝ) * Real.pi / ((n:ℝ) + 2) = Real.pi / ((n:ℝ)/2 + 1) by
      field_simp]
    field_simp
  · positivity
  · positivity

end Commons.Measure.EuclideanSpace