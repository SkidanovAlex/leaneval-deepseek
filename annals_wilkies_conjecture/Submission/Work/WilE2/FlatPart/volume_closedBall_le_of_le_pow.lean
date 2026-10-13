import Mathlib

namespace Work.WilE2.FlatPart

theorem volume_closedBall_le_of_le_pow {n k : ℕ} (hk : n ≤ k) (b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hr5 : r ≤ 1 / 5) {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    MeasureTheory.volume (Metric.closedBall c (ε * (5 * r) ^ k))
      ≤ ENNReal.ofReal (2 * ε * 5 ^ n / 2 ^ n) * MeasureTheory.volume (Metric.ball b r) := by
  have h5r0 : 0 ≤ 5 * r := by linarith
  have h5r1 : 5 * r ≤ 1 := by linarith
  rw [Real.volume_closedBall, Real.volume_pi_ball b hr, Fintype.card_fin]
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * ε * 5 ^ n / 2 ^ n)]
  apply ENNReal.ofReal_le_ofReal
  have hp : (5 * r) ^ k ≤ (5 * r) ^ n := pow_le_pow_of_le_one h5r0 h5r1 hk
  have key : 2 * ε * 5 ^ n / 2 ^ n * (2 * r) ^ n = 2 * ε * (5 * r) ^ n := by
    rw [mul_pow, mul_pow]; field_simp; try ring
  rw [key]
  nlinarith [hp, hε]

end Work.WilE2.FlatPart
