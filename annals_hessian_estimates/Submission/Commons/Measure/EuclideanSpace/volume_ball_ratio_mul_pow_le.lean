import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio

namespace Commons.Measure.EuclideanSpace

open MeasureTheory MeasureTheory.Measure Metric ENNReal

theorem volume_ball_ratio_mul_pow_le {n : ℕ} {s ε : ℝ} (hε : 0 < ε) (hs : 0 < s) (hse : ε ≤ s) :
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n
      ≤ (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal
          * (2 ^ n * ε ^ n) := by
  set c : ℝ := (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hc
  have hc_nonneg : 0 ≤ c := ENNReal.toReal_nonneg
  have hvol : ∀ t : ℝ, 0 < t →
      (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) t)).toReal = t ^ n * c := by
    intro t ht
    have h := addHaar_ball_mul_of_pos MeasureTheory.volume (0 : EuclideanSpace ℝ (Fin n)) ht 1
    rw [mul_one] at h
    rw [h, finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg ht.le n)]
  have h2s : s + ε ≤ 2 * s := by linarith
  have hpow : (s + ε) ^ n ≤ (2 * s) ^ n :=
    pow_le_pow_left₀ (by linarith) h2s n
  have heq : (s ^ n * c) * (2 ^ n * ε ^ n) = (ε ^ n * c) * (2 * s) ^ n := by
    have e1 : (s ^ n * c) * (2 ^ n * ε ^ n) = (s ^ n * 2 ^ n) * (c * ε ^ n) := by ring
    have e2 : s ^ n * 2 ^ n = (s * 2) ^ n := by rw [mul_pow]
    have e3 : (s * 2 : ℝ) = 2 * s := by ring
    rw [e1, e2, e3]
    ring
  calc (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n
      = (ε ^ n * c) * (s + ε) ^ n := by rw [hvol ε hε]
    _ ≤ (ε ^ n * c) * (2 * s) ^ n := by
          exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (pow_nonneg hε.le n) hc_nonneg)
    _ = (s ^ n * c) * (2 ^ n * ε ^ n) := heq.symm
    _ = (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)).toReal
          * (2 ^ n * ε ^ n) := by rw [hvol s hs]

end Commons.Measure.EuclideanSpace