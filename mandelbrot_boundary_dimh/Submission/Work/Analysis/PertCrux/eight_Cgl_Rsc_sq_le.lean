import Mathlib

namespace Work.Analysis.PertCrux

/-- Numeric auxiliary: for `(193:ℝ) < Ξ'` the quantity `8 * Ξ' * (9.6e17 * Ξ'^6)^2` is
dominated by `10^9 * Ξ'^40`.  This is the analytic content of the estimate; the rest is
monotonicity in `Cgl` and `Rsc`. -/
private lemma crux_numeric_core {Ξ' : ℝ} (hΞ' : 193 < Ξ') :
    8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 ≤ 10 ^ 9 * Ξ' ^ 40 := by
  have hΞ0 : (0 : ℝ) < Ξ' := by linarith
  have h193 : (193 : ℝ) ^ 27 ≤ Ξ' ^ 27 := pow_le_pow_left₀ (by norm_num) hΞ'.le 27
  have hbase : 8 * (960000000000000000 : ℝ) ^ 2 ≤ 10 ^ 9 * (193 : ℝ) ^ 27 := by norm_num
  have h1 : 8 * (960000000000000000 : ℝ) ^ 2 ≤ 10 ^ 9 * Ξ' ^ 27 := by
    have h10 : (0 : ℝ) ≤ 10 ^ 9 := by norm_num
    nlinarith [hbase, mul_le_mul_of_nonneg_left h193 h10]
  have h2 : 8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 ≤ 10 ^ 9 * Ξ' ^ 27 * Ξ' ^ 13 :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : 10 ^ 9 * Ξ' ^ 27 * Ξ' ^ 13 = 10 ^ 9 * Ξ' ^ 40 := by ring
  linarith [h2, h3]

theorem eight_Cgl_Rsc_sq_le {Ξ' Cgl Rsc : ℝ} (hΞ' : 193 < Ξ')
    (hCgl0 : 0 < Cgl) (hCglΞ : Cgl ≤ Ξ') (hRsc0 : 0 < Rsc)
    (hRscUB : Rsc ≤ 960000000000000000 * Ξ' ^ 6) :
    8 * Cgl * Rsc ^ 2 ≤ 10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20 := by
  have hΞ0 : (0 : ℝ) < Ξ' := by linarith
  -- Bound on `Rsc ^ 2`.
  have hR2 : Rsc ^ 2 ≤ (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 12 := by
    have h := pow_le_pow_left₀ (le_of_lt hRsc0) hRscUB 2
    calc Rsc ^ 2 ≤ (960000000000000000 * Ξ' ^ 6) ^ 2 := h
      _ = (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 12 := by ring
  -- Bound on `8 * Cgl`.
  have h8 : 8 * Cgl ≤ 8 * Ξ' := by linarith
  have hK : (0 : ℝ) ≤ (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 12 := by positivity
  have hstep1 : 8 * Cgl * Rsc ^ 2 ≤ 8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 := by
    calc 8 * Cgl * Rsc ^ 2
        ≤ (8 * Ξ') * ((960000000000000000 : ℝ) ^ 2 * Ξ' ^ 12) :=
          mul_le_mul h8 hR2 (sq_nonneg Rsc) (by positivity)
      _ = 8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 := by ring
  -- Compare with the huge right-hand side.
  have hstep2 : 8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 ≤ 10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20 := by
    have hpow : Ξ' ^ 40 ≤ (Ξ' ^ 2 + 1) ^ 20 := by
      have hle : Ξ' ^ 2 ≤ Ξ' ^ 2 + 1 := by linarith
      calc Ξ' ^ 40 = (Ξ' ^ 2) ^ 20 := by ring
        _ ≤ (Ξ' ^ 2 + 1) ^ 20 := pow_le_pow_left₀ (by positivity) hle 20
    calc 8 * (960000000000000000 : ℝ) ^ 2 * Ξ' ^ 13 ≤ 10 ^ 9 * Ξ' ^ 40 :=
          crux_numeric_core hΞ'
      _ ≤ 10 ^ 9 * (Ξ' ^ 2 + 1) ^ 20 := by
          exact mul_le_mul_of_nonneg_left hpow (by norm_num)
  linarith [hstep1, hstep2]

end Work.Analysis.PertCrux
