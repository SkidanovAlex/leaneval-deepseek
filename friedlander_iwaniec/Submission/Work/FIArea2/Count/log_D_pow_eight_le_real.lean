import Mathlib

namespace Work.FIArea2.Count

/-- For `D ≤ 33 * Nr` with real `Nr ≥ 1`, the eighth power of `log D + 2` is bounded by
`7^8` times the eighth power of `log (Nr + 2)`. -/
theorem log_D_pow_eight_le_real (D : ℕ) (Nr : ℝ) (hNr : 1 ≤ Nr) (hD : ((D : ℕ) : ℝ) ≤ 33 * Nr) :
    (Real.log ((D : ℕ) : ℝ) + 2) ^ 8 ≤ 7 ^ 8 * (Real.log (Nr + 2)) ^ 8 := by
  -- `log 33 ≤ 4 * log 3`, since `33 ≤ 3^4`.
  have hlog33 : Real.log (33:ℝ) ≤ 4 * Real.log 3 := by
    have h : Real.log (33:ℝ) ≤ Real.log ((3:ℝ)^4) := Real.log_le_log (by norm_num) (by norm_num)
    simpa [Real.log_pow] using h
  -- `1 ≤ log 3`, since `exp 1 < 3`.
  have h1log3 : (1:ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
    exact le_of_lt Real.exp_one_lt_three
  -- `log 3 ≤ log (Nr + 2)`, since `3 ≤ Nr + 2`.
  have h3le : Real.log 3 ≤ Real.log (Nr + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  -- `log D ≤ log (33 * Nr)`.
  have hlogD : Real.log ((D:ℝ)) ≤ Real.log (33 * Nr) := by
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · subst hD0
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast hDpos) hD
  have hlogNr : 0 < Nr := by linarith
  -- The key additive estimate `log D + 2 ≤ 7 * log (Nr + 2)`.
  have key : Real.log ((D:ℝ)) + 2 ≤ 7 * Real.log (Nr + 2) := by
    have hlog33Nr : Real.log (33 * Nr) = Real.log 33 + Real.log Nr :=
      Real.log_mul (by norm_num) (by linarith)
    have hlogNrle : Real.log Nr ≤ Real.log (Nr + 2) :=
      Real.log_le_log hlogNr (by linarith)
    linarith [hlogD, hlog33Nr, hlogNrle, hlog33, h3le, h1log3]
  have hbase_nonneg : 0 ≤ Real.log ((D:ℝ)) + 2 := by
    have : 0 ≤ Real.log ((D:ℝ)) := by
      rcases Nat.eq_zero_or_pos D with hD0 | hDpos
      · subst hD0; simp
      · exact Real.log_nonneg (by exact_mod_cast hDpos)
    linarith
  have hpow := pow_le_pow_left₀ hbase_nonneg key 8
  simpa [mul_pow] using hpow

end Work.FIArea2.Count
