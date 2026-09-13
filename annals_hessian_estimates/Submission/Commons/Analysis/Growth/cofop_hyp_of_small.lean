import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Growth

theorem cofop_hyp_of_small {ε a p c : ℝ} (hε : 0 < ε) (ha : 0 < a) (hp : 0 ≤ p)
    (h : 48 * ε * a * 2 ^ (2 * p + 4) ≤ c) :
    12 * ε * a * 2 ^ (p + 2) ≤ c := by
  have hexp : p + 2 ≤ 2 * p + 4 := by linarith
  have hpow : (2 : ℝ) ^ (p + 2) ≤ 2 ^ (2 * p + 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hεa : (0 : ℝ) ≤ ε * a := le_of_lt (mul_pos hε ha)
  calc 12 * ε * a * 2 ^ (p + 2)
      ≤ 12 * ε * a * 2 ^ (2 * p + 4) := by
        apply mul_le_mul_of_nonneg_left hpow
        positivity
    _ ≤ 48 * ε * a * 2 ^ (2 * p + 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hεa]
    _ ≤ c := h

end Commons.Analysis.Growth