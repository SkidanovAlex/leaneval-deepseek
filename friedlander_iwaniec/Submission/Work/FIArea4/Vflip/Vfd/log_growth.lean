import Mathlib

namespace Work.FIArea4.Vflip.Vfd

/-- Logarithmic factors are dominated by any positive power, uniformly for `H ≥ 1`:
`(log (2H) + 1)^4 ≤ K * H^θ`.  The constant is explicit,
`K = (2^(θ/4) / (θ/4) + 1)^4`, obtained from `log x ≤ x^a / a` with `a = θ/4`
and `1 ≤ H^a`. -/
theorem log_growth (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H → (Real.log (2 * H) + 1) ^ 4 ≤ K * H ^ θ := by
  set a := θ / 4 with ha
  have ha_pos : 0 < a := by rw [ha]; linarith
  have h4a : a * 4 = θ := by rw [ha]; ring
  refine ⟨(2 ^ a / a + 1) ^ (4 : ℝ), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) 4
  · intro H hH
    have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
    have h2Hpos : 0 < 2 * H := by linarith
    have h2H1 : 1 < 2 * H := by linarith
    have hlog : Real.log (2 * H) ≤ (2 * H) ^ a / a :=
      Real.log_le_rpow_div (le_of_lt h2Hpos) ha_pos
    have h2Hpow : (2 * H) ^ a = 2 ^ a * H ^ a :=
      Real.mul_rpow (by norm_num) (le_of_lt hHpos)
    rw [h2Hpow] at hlog
    have hHpow1 : 1 ≤ H ^ a := Real.one_le_rpow hH (le_of_lt ha_pos)
    have hHpowpos : 0 < H ^ a := Real.rpow_pos_of_pos hHpos a
    have hcoef : 0 < 2 ^ a / a + 1 := by positivity
    have hstep : Real.log (2 * H) + 1 ≤ (2 ^ a / a + 1) * H ^ a := by
      have hdiv : (2 ^ a * H ^ a) / a = 2 ^ a / a * H ^ a := by ring
      rw [hdiv] at hlog
      nlinarith [hlog, hHpow1]
    have hnonneg : 0 ≤ Real.log (2 * H) + 1 := by
      have := Real.log_pos h2H1; linarith
    have hr := Real.rpow_le_rpow hnonneg hstep (by norm_num : (0 : ℝ) ≤ 4)
    rw [Real.mul_rpow (le_of_lt hcoef) hHpowpos.le] at hr
    rw [← Real.rpow_mul (le_of_lt hHpos) a 4, h4a] at hr
    rwa [← Real.rpow_natCast]

end Work.FIArea4.Vflip.Vfd
