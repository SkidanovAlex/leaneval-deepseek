import Mathlib
import Submission.Commons.Analysis.ExpLog.const_mul_log_pow_le_rpow_threshold

namespace Work.FIArea7

open Commons.Analysis.ExpLog

/-- The base `log n / log 2 + 1` is eventually dominated by a fixed multiple of `log n`:
for `x ≥ 2`, `log x / log 2 + 1 = (log x + log 2) / log 2 ≤ (2 / log 2) log x`. -/
private lemma logDivLogTwo_add_one_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log x / Real.log 2 + 1 ≤ (2 / Real.log 2) * Real.log x := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h1 : Real.log x / Real.log 2 + 1 = (Real.log x + Real.log 2) / Real.log 2 := by
    rw [add_div, div_self (ne_of_gt hlog2pos)]
  rw [h1]
  have hnum : Real.log x + Real.log 2 ≤ 2 * Real.log x := by linarith
  calc (Real.log x + Real.log 2) / Real.log 2
      ≤ (2 * Real.log x) / Real.log 2 := div_le_div_of_nonneg_right hnum hlog2pos.le
    _ = (2 / Real.log 2) * Real.log x := by ring

/-- Every power of `log n / log 2 + 1` is eventually dominated by any positive power of `n`. -/
theorem logPowBound (c : ℝ) (hc : 0 < c) (B : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log (n : ℝ) / Real.log 2 + 1) ^ B ≤ (n : ℝ) ^ c := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := 2 / Real.log 2 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  -- `C ^ B * (log x) ^ B ≤ x ^ (c/2)` for all large `x`.
  obtain ⟨X, _hX1, hX⟩ :=
    const_mul_log_pow_le_rpow_threshold (K := C ^ B) (pow_nonneg hCpos.le B)
      (n := B) (r := c / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_ge (max X 2)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (max X 2 : ℝ) ≤ (n : ℝ) := le_trans hN hNn
  have hxX : X ≤ (n : ℝ) := le_trans (le_max_left _ _) hnR
  have hx2 : (2 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hnR
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hlogx0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hx1
  have hbase : Real.log (n : ℝ) / Real.log 2 + 1 ≤ C * Real.log (n : ℝ) := by
    rw [hCdef]; exact logDivLogTwo_add_one_le hx2
  have hbase0 : 0 ≤ Real.log (n : ℝ) / Real.log 2 + 1 :=
    add_nonneg (div_nonneg hlogx0 hlog2pos.le) zero_le_one
  calc (Real.log (n : ℝ) / Real.log 2 + 1) ^ B
      ≤ (C * Real.log (n : ℝ)) ^ B := pow_le_pow_left₀ hbase0 hbase B
    _ = C ^ B * (Real.log (n : ℝ)) ^ B := by rw [mul_pow]
    _ ≤ (n : ℝ) ^ (c / 2) := hX _ hxX
    _ ≤ (n : ℝ) ^ c := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

end Work.FIArea7
