import Mathlib

namespace Work.KMTAreas.A5

/-- Polylogarithmic growth bound: for every `P > 0` and `c > 0` there is a constant `K > 0`
with `(max 1 (logb 2 x)) ^ P ≤ K * x ^ (c * P)` for all `x ≥ 1`.

This is the elementary estimate that lets a `⟨Log N⟩^{O(1)}` loss be absorbed by an
arbitrarily small power saving. -/
theorem logbPowLeConstMulRpow {P c : ℝ} (hP : 0 < P) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x →
      (max 1 (Real.logb 2 x)) ^ P ≤ K * x ^ (c * P) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hclog2 : 0 < c * Real.log 2 := mul_pos hc hlog2
  refine ⟨(1 + 1 / (c * Real.log 2)) ^ P, ?_, ?_⟩
  · apply Real.rpow_pos_of_pos
    have : 0 < 1 / (c * Real.log 2) := by positivity
    linarith
  · intro x hx
    have hx0 : 0 ≤ x := by linarith
    have hxc1 : 1 ≤ x ^ c := Real.one_le_rpow hx (le_of_lt hc)
    have hxc0 : 0 ≤ x ^ c := le_trans zero_le_one hxc1
    -- `log₂ x ≤ x ^ c / (c log 2)`
    have hlb : Real.logb 2 x ≤ x ^ c / (c * Real.log 2) := by
      have h1 : Real.log x ≤ x ^ c / c := Real.log_le_rpow_div hx0 hc
      have h2 : Real.log x / Real.log 2 ≤ (x ^ c / c) / Real.log 2 :=
        div_le_div_of_nonneg_right h1 (le_of_lt hlog2)
      have h3 : (x ^ c / c) / Real.log 2 = x ^ c / (c * Real.log 2) := by rw [div_div]
      exact h2.trans (le_of_eq h3)
    -- `max 1 (log₂ x) ≤ (1 + 1/(c log 2)) * x ^ c`
    have hmax : max 1 (Real.logb 2 x) ≤ (1 + 1 / (c * Real.log 2)) * x ^ c := by
      have hA0 : 0 ≤ x ^ c / (c * Real.log 2) := div_nonneg hxc0 (le_of_lt hclog2)
      have h1 : max 1 (Real.logb 2 x) ≤ 1 + x ^ c / (c * Real.log 2) :=
        max_le (by linarith) (by linarith)
      have h2 : 1 + x ^ c / (c * Real.log 2) ≤ (1 + 1 / (c * Real.log 2)) * x ^ c := by
        have hdm : x ^ c / (c * Real.log 2) = (1 / (c * Real.log 2)) * x ^ c := by
          rw [div_eq_mul_one_div, mul_comm]
        rw [hdm, add_mul, one_mul]
        linarith
      linarith
    calc (max 1 (Real.logb 2 x)) ^ P
        ≤ ((1 + 1 / (c * Real.log 2)) * x ^ c) ^ P :=
          Real.rpow_le_rpow (le_trans zero_le_one (le_max_left 1 _)) hmax (le_of_lt hP)
      _ = (1 + 1 / (c * Real.log 2)) ^ P * (x ^ c) ^ P := by
          rw [Real.mul_rpow (by positivity) hxc0]
      _ = (1 + 1 / (c * Real.log 2)) ^ P * x ^ (c * P) := by
          rw [← Real.rpow_mul hx0]

end Work.KMTAreas.A5
