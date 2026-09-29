import Mathlib

/-! # The odd part of the logarithm series

`∑_{i} v ^ (2i+1) / (2i+1) = ½ log ((1+v)/(1-v))` for `|v| < 1`: this is
`Real.hasSum_log_sub_log_of_abs_lt_one` (the series of `log(1+v) - log(1-v)`)
rescaled by `1/2` and rewritten with `Real.log_div`. -/

namespace Work.ANum

theorem hasSum_log_div {v : ℝ} (hv : |v| < 1) :
    HasSum (fun i : ℕ => v ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))
      (1 / 2 * Real.log ((1 + v) / (1 - v))) := by
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  have hpos1 : 0 < 1 + v := by linarith
  have hpos2 : 0 < 1 - v := by linarith
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2 : ℝ)
  have hkey : (1 / 2 : ℝ) * (Real.log (1 + v) - Real.log (1 - v))
      = 1 / 2 * Real.log ((1 + v) / (1 - v)) := by
    rw [Real.log_div (ne_of_gt hpos1) (ne_of_gt hpos2)]
  rw [hkey] at h
  exact h.congr_fun (fun i => by push_cast; ring)

end Work.ANum
