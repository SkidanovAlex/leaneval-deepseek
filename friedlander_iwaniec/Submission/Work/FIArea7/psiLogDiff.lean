import Mathlib

namespace Work.FIArea7

/-- For `n ≥ 2`, `|1/log n - 1/log (n+1)| ≤ 1/(n (log n)^2)`. -/
theorem psiLogDiff {n : ℕ} (hn : 2 ≤ n) :
    |1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)|
      ≤ 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have ha : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hb : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hnpos (by linarith)
  -- `log (n+1) - log n = log (1 + 1/n) ≤ 1/n`
  have hba : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have hx : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := div_pos hn1pos hnpos
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by linarith) (by linarith)] at h
    have h2 : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      rw [add_div, div_self (ne_of_gt hnpos)]
      ring
    linarith [h, h2]
  -- put the difference over a common denominator
  have heq : (1 : ℝ) / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)
      = (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
          / (Real.log (n : ℝ) * Real.log ((n : ℝ) + 1)) := by
    rw [one_div, one_div]
    exact inv_sub_inv (ne_of_gt ha) (ne_of_gt hb)
  have hnonneg : 0 ≤ (1 : ℝ) / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1) := by
    rw [heq]
    exact div_nonneg (by linarith) (le_of_lt (mul_pos ha hb))
  -- cross-multiplied form of the goal
  have hmain : (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) * ((n : ℝ) * Real.log (n : ℝ) ^ 2)
      ≤ 1 * (Real.log (n : ℝ) * Real.log ((n : ℝ) + 1)) := by
    have step1 : ((n : ℝ) * Real.log (n : ℝ)) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ ((n : ℝ) * Real.log (n : ℝ)) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hba (le_of_lt (mul_pos hnpos ha))
    have step2 : ((n : ℝ) * Real.log (n : ℝ)) * (1 / (n : ℝ)) = Real.log (n : ℝ) := by
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      field_simp
    have hmul : ((n : ℝ) * Real.log (n : ℝ)) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ Real.log ((n : ℝ) + 1) := by linarith [step1, step2, hle]
    have hmul2 : Real.log (n : ℝ) * (((n : ℝ) * Real.log (n : ℝ)) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)))
        ≤ Real.log (n : ℝ) * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hmul (le_of_lt ha)
    nlinarith [hmul2]
  rw [abs_of_nonneg hnonneg, heq]
  rw [le_div_iff₀ (mul_pos hnpos (pow_pos ha 2))]
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ (mul_pos ha hb)]
  exact hmain

end Work.FIArea7
