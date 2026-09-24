import Mathlib

namespace Work.GM.Affine

/-- Auxiliary power bound: for `T ≥ 1`, `0 < α`, `M₃ ≥ T^4`, `δ + 4 ≤ N α` and
`δ + 4 ≤ 4 N`, the sum `(2/T^α)^N + 4·2^N/M₃^N` is at most `5·2^N·T^{-(δ+4)}`.
The first term is bounded by `2^N·T^{-(δ+4)}` using `Nα ≥ δ+4`, and the second
by `4·2^N·T^{-(δ+4)}` using `M₃^N ≥ T^{4N} ≥ T^{δ+4}`. -/
theorem pow_bound_aux {T α δ M₃ : ℝ} {N : ℕ} (hT : 1 ≤ T) (hα : 0 < α)
    (hM₃ : T ^ 4 ≤ M₃) (hNα : δ + 4 ≤ (N : ℝ) * α) (hN4 : δ + 4 ≤ 4 * (N : ℝ)) :
    (1 / (T ^ α / 2)) ^ N + 4 * 2 ^ N / M₃ ^ N ≤ 5 * 2 ^ N * T ^ (-(δ + 4)) := by
  -- `hα` is not needed for the estimate; keep a reference so the hypothesis is "used".
  have hαpos : 0 < α := hα
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTnn : 0 ≤ T := hTpos.le
  have hExp : (T ^ (-α)) ^ N = T ^ (-((N : ℝ) * α)) := by
    rw [← Real.rpow_natCast (T ^ (-α)) N, ← Real.rpow_mul hTnn]
    ring_nf
  -- Bound on the first summand: `(2/T^α)^N ≤ 2^N T^{-(δ+4)}`.
  have hA : (1 / (T ^ α / 2)) ^ N ≤ 2 ^ N * T ^ (-(δ + 4)) := by
    have heq : (1 / (T ^ α / 2)) ^ N = 2 ^ N * T ^ (-((N : ℝ) * α)) := by
      rw [one_div, inv_div, div_eq_mul_inv, ← Real.rpow_neg hTnn α, mul_pow, hExp]
    rw [heq]
    have hNα' : -((N : ℝ) * α) ≤ -(δ + 4) := by linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hNα') (by positivity)
  -- `M₃^N ≥ T^{4N}` and `T^{4N} ≥ T^{δ+4}`, hence `T^{δ+4} ≤ M₃^N`.
  have hT4le1 : 1 ≤ T ^ 4 := one_le_pow₀ hT
  have hT4N : (T ^ 4) ^ N = T ^ (4 * (N : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast T (4 * N)]
    push_cast
    ring_nf
  have h3 : (T ^ 4) ^ N ≤ M₃ ^ N := pow_le_pow_left₀ (by positivity) hM₃ N
  have hTpowle : T ^ (δ + 4) ≤ M₃ ^ N := by
    have h1 : T ^ (δ + 4) ≤ T ^ (4 * (N : ℝ)) := Real.rpow_le_rpow_of_exponent_le hT hN4
    rw [← hT4N] at h1
    exact h1.trans h3
  have hTpowpos : 0 < T ^ (δ + 4) := Real.rpow_pos_of_pos hTpos _
  have hle0 : 1 / M₃ ^ N ≤ 1 / T ^ (δ + 4) := one_div_le_one_div_of_le hTpowpos hTpowle
  have hle : 1 / M₃ ^ N ≤ T ^ (-(δ + 4)) := by
    simpa only [one_div, Real.rpow_neg hTnn] using hle0
  -- Bound on the second summand: `4·2^N/M₃^N ≤ 4·2^N T^{-(δ+4)}`.
  have hB : 4 * 2 ^ N / M₃ ^ N ≤ 4 * 2 ^ N * T ^ (-(δ + 4)) := by
    rw [div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  calc
    (1 / (T ^ α / 2)) ^ N + 4 * 2 ^ N / M₃ ^ N
        ≤ 2 ^ N * T ^ (-(δ + 4)) + 4 * 2 ^ N * T ^ (-(δ + 4)) := add_le_add hA hB
    _ = 5 * 2 ^ N * T ^ (-(δ + 4)) := by ring

end Work.GM.Affine
