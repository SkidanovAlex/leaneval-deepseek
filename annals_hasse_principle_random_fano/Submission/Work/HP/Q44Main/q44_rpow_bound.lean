import Mathlib
import Submission.Work.HP.ceil_logb_bounds

namespace Work.HP.Q44Main

/-- Auxiliary arithmetic bound: for `Δ ≥ 1`, `(Δ + 1)^3 ≤ 8 * Δ^3`. -/
private lemma delta_cube_le (Δ : ℝ) (hΔ : 1 ≤ Δ) : (Δ + 1) ^ 3 ≤ 8 * Δ ^ 3 := by
  have hd1 : Δ + 1 ≤ 2 * Δ := by linarith
  calc (Δ + 1) ^ 3 ≤ (2 * Δ) ^ 3 := pow_le_pow_left₀ (by linarith) hd1 3
    _ = 8 * Δ ^ 3 := by ring

/-- Auxiliary arithmetic bound: `4096 * K * (Δ+1)^3 ≤ 32768 * K * Δ^3` for `K ≥ 0`, `Δ ≥ 1`. -/
private lemma scaled_delta_cube_le (K Δ : ℝ) (hK : 0 ≤ K) (hΔ : 1 ≤ Δ) :
    4096 * K * (Δ + 1) ^ 3 ≤ 32768 * K * Δ ^ 3 := by
  have hcube : (Δ + 1) ^ 3 ≤ 8 * Δ ^ 3 := delta_cube_le Δ hΔ
  have h := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 4096 * K)
  calc 4096 * K * (Δ + 1) ^ 3 ≤ 4096 * K * (8 * Δ ^ 3) := h
    _ = 32768 * K * Δ ^ 3 := by ring

theorem q44_rpow_bound (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ) :
    (2 : ℝ) ^ (3 * ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊) ≤ 32768 * Kmink ^ 3 * Δ ^ 3 := by
  set n : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hn
  have hx1 : 1 ≤ 8 * Kmink * (Δ + 1) := by nlinarith
  have hle : (2 : ℝ) ^ n ≤ 2 * (8 * Kmink * (Δ + 1)) := (Work.HP.ceil_logb_bounds hx1).2
  rw [show 3 * n = n * 3 by ring, pow_mul]
  have h2nn : (0 : ℝ) ≤ 2 ^ n := pow_nonneg (by norm_num) n
  calc ((2 : ℝ) ^ n) ^ 3
      ≤ (2 * (8 * Kmink * (Δ + 1))) ^ 3 := pow_le_pow_left₀ h2nn hle 3
    _ = 4096 * Kmink ^ 3 * (Δ + 1) ^ 3 := by ring
    _ ≤ 32768 * Kmink ^ 3 * Δ ^ 3 :=
        scaled_delta_cube_le (Kmink ^ 3) Δ (pow_nonneg (by linarith) 3) hΔ

end Work.HP.Q44Main
