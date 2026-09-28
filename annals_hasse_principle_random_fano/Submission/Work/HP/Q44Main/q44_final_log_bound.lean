import Mathlib
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.Q44Main.q44_rpow_bound
import Submission.Work.HP.Q44Main.q44_log_sq_bound

namespace Work.HP.Q44Main

/-- Final logarithmic bound for the Q44 estimate: for every `Kmink ≥ 1` there is `K > 0` with
`4 (⌈logb 2 (8 Kmink (Δ+1))⌉₊ + 1)^2 · 2^(3 ⌈logb 2 (8 Kmink (Δ+1))⌉₊) ≤ K Δ^3 (log (2Δ))^2`
for all real `Δ ≥ 1`.

The exponential factor is controlled by `q44_rpow_bound`, the polylogarithmic factor by
`q44_log_sq_bound`, and the two are combined with the constant
`K = 4 · 32768 · Kmink^3 · (logb 2 (8 Kmink) + 3)^2 / (log 2)^2`. -/
theorem q44_final_log_bound (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      4 * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2
        * (2 : ℝ) ^ (3 * ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊)
      ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKm : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  refine ⟨4 * 32768 * Kmink ^ 3 * (Real.logb 2 (8 * Kmink) + 3) ^ 2 / (Real.log 2) ^ 2, ?_, ?_⟩
  · have hA3pos : 0 < Real.logb 2 (8 * Kmink) + 3 := by
      have h1 : 0 ≤ Real.logb 2 (8 * Kmink) :=
        Real.logb_nonneg (by norm_num) (by nlinarith [hKmink])
      linarith
    have h1 : (0 : ℝ) < Kmink ^ 3 := pow_pos hKm 3
    have h2 : (0 : ℝ) < (Real.logb 2 (8 * Kmink) + 3) ^ 2 := pow_pos hA3pos 2
    have h3 : (0 : ℝ) < 4 * 32768 * Kmink ^ 3 := by
      have : (0 : ℝ) < 4 * 32768 := by norm_num
      exact mul_pos this h1
    exact div_pos (mul_pos h3 h2) (pow_pos hlog2 2)
  · intro Δ hΔ
    have hΔpos : 0 < Δ := by linarith
    have hrpow := q44_rpow_bound Kmink Δ hKmink hΔ
    have hlogsq := q44_log_sq_bound Kmink Δ hKmink hΔ
    have hfac : (0 : ℝ) ≤ 4 * (32768 * Kmink ^ 3 * Δ ^ 3) := by
      have h1 : (0 : ℝ) < Kmink ^ 3 := pow_pos hKm 3
      have h2 : (0 : ℝ) < Δ ^ 3 := pow_pos hΔpos 3
      have h3 : (0 : ℝ) < 32768 * Kmink ^ 3 * Δ ^ 3 := by
        have h4 : (0 : ℝ) < 32768 * Kmink ^ 3 := by
          have : (0 : ℝ) < 32768 := by norm_num
          exact mul_pos this h1
        exact mul_pos h4 h2
      exact le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 4) h3)
    calc 4 * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2
            * (2 : ℝ) ^ (3 * ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊)
        = (4 * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2)
            * (2 : ℝ) ^ (3 * ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊) := by ring
      _ ≤ (4 * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2)
            * (32768 * Kmink ^ 3 * Δ ^ 3) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = 4 * (32768 * Kmink ^ 3 * Δ ^ 3)
            * ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2 := by ring
      _ ≤ 4 * (32768 * Kmink ^ 3 * Δ ^ 3)
            * (((Real.logb 2 (8 * Kmink) + 3) ^ 2 / (Real.log 2) ^ 2)
                * (Real.log (2 * Δ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hlogsq hfac
      _ = (4 * 32768 * Kmink ^ 3 * (Real.logb 2 (8 * Kmink) + 3) ^ 2 / (Real.log 2) ^ 2)
            * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by ring

end Work.HP.Q44Main
