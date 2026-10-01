import Mathlib

namespace Work.ZeroDensity.Ingham

/-- **Absorbing a logarithmic factor into `T ^ ε`.**  For every `ε > 0` the quantity
`log (T + 2) + 2` is `≪_ε T ^ ε` for `T ≥ 2`. -/
theorem logAddTwoLeRpow {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 2 ≤ T → Real.log (T + 2) + 2 ≤ K * T ^ ε := by
  -- Explicit constant: the two competing contributions are `log 2 + 2` (bounded on
  -- `T ≥ 2` by the growth of `T ^ ε` from the value `2 ^ ε`) and `log T` (bounded by
  -- `T ^ ε / ε` via `Real.log_le_rpow_div`).
  refine ⟨(Real.log 2 + 2) / 2 ^ ε + 1 / ε, ?_, ?_⟩
  · have h1 : 0 < Real.log 2 + 2 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
    have h2 : 0 < (2:ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
    have h3 : 0 < (Real.log 2 + 2) / 2 ^ ε := div_pos h1 h2
    have h4 : 0 < 1 / ε := by positivity
    linarith
  · intro T hT
    have hTpos : 0 < T := by linarith
    have hT2pos : 0 < T + 2 := by linarith
    -- `T + 2 ≤ 2 * T` for `T ≥ 2`, so `log (T + 2) ≤ log 2 + log T`.
    have hle : T + 2 ≤ 2 * T := by linarith
    have hlogmono : Real.log (T + 2) ≤ Real.log (2 * T) := Real.log_le_log hT2pos hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hTpos)] at hlogmono
    -- `log T ≤ T ^ ε / ε`.
    have hlogT : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hTpos.le hε
    -- `2 ^ ε ≤ T ^ ε`.
    have hpow2 : (2:ℝ) ^ ε ≤ T ^ ε := Real.rpow_le_rpow (by norm_num) hT hε.le
    have hc1 : 0 < (Real.log 2 + 2) := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
    have hc2 : 0 < (2:ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
    -- The constant part is absorbed by `T ^ ε`.
    have hconst : Real.log 2 + 2 ≤ ((Real.log 2 + 2) / 2 ^ ε) * T ^ ε := by
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ hc2]
      have := mul_le_mul_of_nonneg_left hpow2 hc1.le
      linarith [this]
    have hsum : Real.log (T + 2) + 2 ≤ ((Real.log 2 + 2) / 2 ^ ε) * T ^ ε + T ^ ε / ε := by
      linarith
    have hfin : ((Real.log 2 + 2) / 2 ^ ε) * T ^ ε + T ^ ε / ε
        = ((Real.log 2 + 2) / 2 ^ ε + 1 / ε) * T ^ ε := by ring
    linarith [hfin ▸ hsum]

end Work.ZeroDensity.Ingham
