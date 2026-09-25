import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

namespace Work.RHContract.A.regionII

/-- `log Pf ≤ L/2 + 0.15` for `ξ ≥ 10^5`, where `Pf = ⌊1.15 √ξ⌋₊` and `L = log ξ`.
This is the elementary bound used in the boundary-loss estimate: `Pf ≤ 1.15 √ξ`, hence
`log Pf ≤ log 1.15 + (log ξ)/2 ≤ 0.15 + (log ξ)/2`. -/
theorem netLossLogPf (ξ : ℝ) (hξ : 0 < ξ) (hlo : (100000 : ℝ) ≤ ξ) :
    Real.log (netPf ξ : ℝ) ≤ Real.log ξ / 2 + 15 / 100 := by
  unfold netPf
  have hsqrt0 : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ
  -- `√ξ ≥ 300`, so the argument of the floor is at least `345 ≥ 1`.
  have h300 : (300 : ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξ)]
    linarith
  have h1le : (1 : ℝ) ≤ (115 / 100 : ℝ) * Real.sqrt ξ := by nlinarith [h300]
  have hPfpos : 0 < (⌊(115 / 100 : ℝ) * Real.sqrt ξ⌋₊ : ℝ) := by
    have : 0 < ⌊(115 / 100 : ℝ) * Real.sqrt ξ⌋₊ := Nat.floor_pos.mpr h1le
    exact_mod_cast this
  have hle : (⌊(115 / 100 : ℝ) * Real.sqrt ξ⌋₊ : ℝ) ≤ (115 / 100 : ℝ) * Real.sqrt ξ :=
    Nat.floor_le (by positivity)
  have hlog1 : Real.log (⌊(115 / 100 : ℝ) * Real.sqrt ξ⌋₊ : ℝ)
      ≤ Real.log ((115 / 100 : ℝ) * Real.sqrt ξ) := Real.log_le_log hPfpos hle
  have hlog2 : Real.log ((115 / 100 : ℝ) * Real.sqrt ξ)
      = Real.log (115 / 100) + Real.log ξ / 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hsqrt0), Real.log_sqrt (le_of_lt hξ)]
  rw [hlog2] at hlog1
  have hlog115 : Real.log (115 / 100) ≤ 15 / 100 := net_log_115_le
  linarith

end Work.RHContract.A.regionII
