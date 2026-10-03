import Mathlib

namespace Work.FIArea2.Count

/-- Crude logarithmic bound: on the region `2R + 1 ≤ 8√Nr` with `R ≥ 0`, `Nr ≥ 1`
the quantity `log(2R² + 2) + 2` is bounded by a universal constant multiple of
`log(Nr + 2)`, and hence the eighth powers satisfy the same bound. -/
theorem ZAc_log :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (Nr : ℝ),
      0 ≤ R → 1 ≤ Nr → (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr →
      (Real.log (2 * (R : ℝ) ^ 2 + 2) + 2) ^ 8 ≤ C * (Real.log (Nr + 2)) ^ 8 := by
  refine ⟨((Real.log 32 + 2) / Real.log 3 + 1) ^ 8, ?_, ?_⟩
  · apply pow_pos
    have h32 : (0 : ℝ) < Real.log 32 := Real.log_pos (by norm_num)
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hq : 0 < (Real.log 32 + 2) / Real.log 3 := div_pos (by linarith) h3
    linarith
  · intro R Nr hR hNr hbd
    have hNr0 : (0 : ℝ) < Nr := by linarith
    have hr0 : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    -- `R ≤ 4√Nr` and hence `R² ≤ 16 Nr`
    have hr_le : (R : ℝ) ≤ 4 * Real.sqrt Nr := by nlinarith [hbd]
    have hsq : (R : ℝ) ^ 2 ≤ 16 * Nr := by
      have h1 : (R : ℝ) ^ 2 ≤ (4 * Real.sqrt Nr) ^ 2 := pow_le_pow_left₀ hr0 hr_le 2
      have h2 : (4 * Real.sqrt Nr) ^ 2 = 16 * Nr := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hNr0)]
        norm_num
      rw [h2] at h1
      exact h1
    -- `2R² + 2 ≤ 32 (Nr + 2)`
    have hle32 : 2 * (R : ℝ) ^ 2 + 2 ≤ 32 * (Nr + 2) := by nlinarith [hsq]
    have hlog_le : Real.log (2 * (R : ℝ) ^ 2 + 2) ≤ Real.log (32 * (Nr + 2)) := by
      apply Real.log_le_log
      · nlinarith [sq_nonneg (R : ℝ)]
      · exact hle32
    have hlogmul : Real.log (32 * (Nr + 2)) = Real.log 32 + Real.log (Nr + 2) := by
      rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (by linarith : Nr + 2 ≠ 0)]
    rw [hlogmul] at hlog_le
    -- `log 3 ≤ log (Nr + 2)`
    have hlogNr : Real.log 3 ≤ Real.log (Nr + 2) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ Nr + 2)
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h32 : (0 : ℝ) < Real.log 32 := Real.log_pos (by norm_num)
    have hq2 : 0 < ((Real.log 32 + 2) / Real.log 3) := div_pos (by linarith) h3
    -- absorb the additive constant `log 32 + 2` into a multiple of `log (Nr + 2)`
    have hAB : (Real.log 32 + 2) ≤ ((Real.log 32 + 2) / Real.log 3) * Real.log (Nr + 2) := by
      have h2 : ((Real.log 32 + 2) / Real.log 3) * Real.log 3 = Real.log 32 + 2 := by
        field_simp
      calc Real.log 32 + 2 = ((Real.log 32 + 2) / Real.log 3) * Real.log 3 := h2.symm
        _ ≤ ((Real.log 32 + 2) / Real.log 3) * Real.log (Nr + 2) :=
            mul_le_mul_of_nonneg_left hlogNr (le_of_lt hq2)
    have hXY : Real.log (2 * (R : ℝ) ^ 2 + 2) + 2 ≤
        ((Real.log 32 + 2) / Real.log 3 + 1) * Real.log (Nr + 2) := by
      nlinarith [hlog_le, hAB]
    -- raise both sides to the eighth power
    have hXpos : 0 ≤ Real.log (2 * (R : ℝ) ^ 2 + 2) + 2 := by
      have : (0 : ℝ) < Real.log (2 * (R : ℝ) ^ 2 + 2) :=
        Real.log_pos (by nlinarith [sq_nonneg (R : ℝ)])
      linarith
    have h := pow_le_pow_left₀ hXpos hXY 8
    rw [mul_pow] at h
    exact h

end Work.FIArea2.Count
