import Mathlib
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div

open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.ExpLog

/-- Absorbing a log factor into an arbitrary positive power of `y`: for every
`ε > 0` there is `C > 0` with `1 + log(y+1) ≤ C·y^ε` for all `y ≥ 1`. -/
theorem log_absorption {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, (1 : ℝ) ≤ y → 1 + Real.log (y + 1) ≤ C * y ^ ε := by
  let C : ℝ := 1 + (2 : ℝ) ^ ε / ε
  refine ⟨C, ?pos, ?bd⟩
  · dsimp [C]
    have h2 : 0 < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
    have h2e : 0 < (2 : ℝ) ^ ε / ε := div_pos h2 hε
    linarith
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
    have hy0le : 0 ≤ y := hy0.le
    have hy1 : 1 ≤ y + 1 := by linarith
    have hy1nonneg : 0 ≤ y + 1 := by linarith
    have hlog : Real.log (y + 1) ≤ (y + 1) ^ ε / ε := log_le_rpow_div hy1 hε
    have hpow : (y + 1) ^ ε ≤ (2 * y) ^ ε :=
      Real.rpow_le_rpow hy1nonneg (by nlinarith) hε.le
    have hlog2 : Real.log (y + 1) ≤ (2 * y) ^ ε / ε :=
      le_trans hlog ((div_le_div_iff_of_pos_right hε).mpr hpow)
    have h1 : 1 ≤ y ^ ε := Real.one_le_rpow hy hε.le
    dsimp [C]
    calc
      1 + Real.log (y + 1) ≤ 1 + (2 * y) ^ ε / ε := add_le_add_right hlog2 1
      _ = 1 + ((2 : ℝ) ^ ε * y ^ ε) / ε := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy0le]
      _ = 1 + y ^ ε * ((2 : ℝ) ^ ε / ε) := by
        field_simp [hε.ne']
      _ ≤ y ^ ε + y ^ ε * ((2 : ℝ) ^ ε / ε) := add_le_add h1 le_rfl
      _ = (1 + (2 : ℝ) ^ ε / ε) * y ^ ε := by ring

end Commons.Analysis.ExpLog
