import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Lp

theorem rpow_marcinkiewicz_const_le {p A0 A1 Amax K : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hA1 : 0 < A1) (hAmax : 0 < Amax) (hK : 1 ≤ K) (hA0 : 0 < A0)
    (hA0le : A0 ≤ Amax * K) :
    (12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p) ≤
      (12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p) * K := by
  have hp1pos : (0:ℝ) < p - 1 := by linarith
  have hp2pos : (0:ℝ) < 2 - p := by linarith
  have hp_pos : (0:ℝ) < p := by linarith
  have hc0 : (0:ℝ) ≤ 12 * 2 ^ (p - 1) / (p - 1) := by positivity
  have hd0 : (0:ℝ) ≤ 16 * A1 ^ 2 / (2 - p) := by positivity
  have hA0nonneg : (0:ℝ) ≤ 12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p) := by
    positivity
  have hBnonneg : (0:ℝ) ≤ 12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p) := by
    positivity
  have hK0 : (0:ℝ) ≤ K := le_trans zero_le_one hK
  have hAK : 12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p) ≤
      (12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) * K := by
    have h1 : 12 * A0 * 2 ^ (p - 1) / (p - 1) ≤ 12 * Amax * 2 ^ (p - 1) / (p - 1) * K := by
      rw [show 12 * A0 * 2 ^ (p - 1) / (p - 1) = (12 * 2 ^ (p - 1) / (p - 1)) * A0 by ring,
          show 12 * Amax * 2 ^ (p - 1) / (p - 1) * K =
            (12 * 2 ^ (p - 1) / (p - 1)) * (Amax * K) by ring]
      exact mul_le_mul_of_nonneg_left hA0le hc0
    have h2 : 16 * A1 ^ 2 / (2 - p) ≤ 16 * A1 ^ 2 / (2 - p) * K :=
      le_mul_of_one_le_right hd0 hK
    have hsplit : (12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) * K =
        12 * Amax * 2 ^ (p - 1) / (p - 1) * K + 16 * A1 ^ 2 / (2 - p) * K := by ring
    rw [hsplit]; linarith
  have hsle : (1:ℝ) / p ≤ 1 := by
    rw [div_le_one hp_pos]; linarith
  calc (12 * A0 * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p)
      ≤ ((12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) * K) ^ (1 / p) :=
        Real.rpow_le_rpow hA0nonneg hAK (by positivity)
    _ = (12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p) * K ^ (1 / p) :=
        Real.mul_rpow hBnonneg hK0
    _ ≤ (12 * Amax * 2 ^ (p - 1) / (p - 1) + 16 * A1 ^ 2 / (2 - p)) ^ (1 / p) * K := by
        have hKpow : K ^ (1 / p) ≤ K := by
          have h := Real.rpow_le_rpow_of_exponent_le hK hsle
          rwa [Real.rpow_one] at h
        exact mul_le_mul_of_nonneg_left hKpow (Real.rpow_nonneg hBnonneg _)

end Commons.Analysis.Lp