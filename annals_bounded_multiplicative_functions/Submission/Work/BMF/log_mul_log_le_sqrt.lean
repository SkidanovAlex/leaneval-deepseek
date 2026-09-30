import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For all sufficiently large `P ≥ 2`, `log P * log (2P) ≤ sqrt P`.

The logarithmic factor grows like `(log P)^2`, eventually dominated by `P^{1/2}`.
Concretely we take `P₀ = 128^4`. Using `log x ≤ 8 x^{1/8}` (from
`Real.log_le_rpow_div` with `ε = 1/8`) for `x ≥ 0`, we get
`log P * log (2P) ≤ 8 P^{1/8} · 16 P^{1/8} = 128 P^{1/4}`,
and `128 ≤ P^{1/4}` when `P ≥ 128^4`, so `128 P^{1/4} ≤ P^{1/4}·P^{1/4} = sqrt P`. -/
theorem log_mul_log_le_sqrt :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      Real.log P * Real.log (2 * P) ≤ Real.sqrt P := by
  refine ⟨(128:ℝ)^4, by norm_num, ?_⟩
  intro P hP
  have hP2 : (2:ℝ) ≤ P := by
    have h : (2:ℝ) ≤ (128:ℝ)^4 := by norm_num
    linarith
  have hPpos : 0 < P := by linarith
  have hPnonneg : 0 ≤ P := le_of_lt hPpos
  -- `log P ≤ 8 * P^{1/8}`
  have hlogP : Real.log P ≤ 8 * P ^ ((1:ℝ)/8) := by
    have h := Real.log_le_rpow_div hPnonneg (show (0:ℝ) < 1/8 by norm_num)
    calc Real.log P ≤ P ^ ((1:ℝ)/8) / (1/8) := h
      _ = 8 * P ^ ((1:ℝ)/8) := by ring
  -- `log (2P) ≤ 16 * P^{1/8}`
  have hlog2P : Real.log (2*P) ≤ 16 * P ^ ((1:ℝ)/8) := by
    have h2P : 0 ≤ 2 * P := by linarith
    have h := Real.log_le_rpow_div h2P (show (0:ℝ) < 1/8 by norm_num)
    have hmul : (2*P) ^ ((1:ℝ)/8) = 2^((1:ℝ)/8) * P^((1:ℝ)/8) :=
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hPnonneg
    have h2r : (2:ℝ)^((1:ℝ)/8) ≤ 2 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
        (show (1:ℝ)/8 ≤ 1 by norm_num)
      simpa using hh
    calc Real.log (2*P) ≤ (2*P)^((1:ℝ)/8) / (1/8) := h
      _ = 8 * (2^((1:ℝ)/8) * P^((1:ℝ)/8)) := by rw [hmul]; ring
      _ ≤ 8 * (2 * P^((1:ℝ)/8)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
          exact mul_le_mul_of_nonneg_right h2r (by positivity)
      _ = 16 * P^((1:ℝ)/8) := by ring
  have hlog2P_nonneg : 0 ≤ Real.log (2*P) := Real.log_nonneg (by linarith)
  -- `128 ≤ P^{1/4}` since `P ≥ 128^4`
  have h128 : (128:ℝ) ≤ P ^ ((1:ℝ)/4) := by
    have hbase : ((128:ℝ)^4) ^ ((1:ℝ)/4) ≤ P ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hP (by norm_num)
    have heq : ((128:ℝ)^4) ^ ((1:ℝ)/4) = 128 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 128)]
      norm_num
    linarith [hbase, heq]
  calc Real.log P * Real.log (2*P)
      ≤ 8 * P^((1:ℝ)/8) * (16 * P^((1:ℝ)/8)) :=
        mul_le_mul hlogP hlog2P hlog2P_nonneg (by positivity)
    _ = 128 * P^((1:ℝ)/4) := by
        rw [show (8:ℝ) * P^((1:ℝ)/8) * (16 * P^((1:ℝ)/8)) =
              128 * (P^((1:ℝ)/8) * P^((1:ℝ)/8)) by ring,
            show P^((1:ℝ)/8) * P^((1:ℝ)/8) = P^((1:ℝ)/4) by
              rw [← Real.rpow_add hPpos]; norm_num]
    _ ≤ P^((1:ℝ)/4) * P^((1:ℝ)/4) := mul_le_mul_of_nonneg_right h128 (by positivity)
    _ = Real.sqrt P := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hPpos]; norm_num

end Work.BMF
