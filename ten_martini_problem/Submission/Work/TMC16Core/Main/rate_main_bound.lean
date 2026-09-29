import Mathlib
import Submission.Work.TMC16Core.Assembly.Consts
import Submission.Work.TMC16Core.CF.cf_data_bridge

namespace Work.TMC16Core.Main

/-- Rate/bookkeeping estimate for the main bound.

From `(q n)^{8/9} ≤ 2 · s · q(n-1)`, taking logarithms gives
`log s ≥ (8/9) log(q n) - log 2 - log(q(n-1))`, hence
`log((q n)/s) ≤ (1/9) log(q n) + log 2 + log(q(n-1))`.
Combining with `log(q n) ≤ (b₀+ε') q(n-1)` and multiplying by `2/q(n-1) > 0`
yields the claimed bound. -/
theorem rate_main_bound {b₀ ε' : ℝ} {q : ℕ → ℕ} {n s : ℕ}
    (hs : 1 ≤ s) (hsQ8 : (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ))
    (hqn : 1 ≤ (q n : ℝ)) (hQ : 0 < (q (n - 1) : ℝ))
    (hlogq : Real.log (q n : ℝ) ≤ (b₀ + ε') * (q (n - 1) : ℝ)) :
    2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
      ≤ (2 / 9) * (b₀ + ε') + 2 * Real.log 2 / (q (n - 1) : ℝ)
        + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ) := by
  have ha : (0:ℝ) < (q n : ℝ) := by linarith
  have hsr : (0:ℝ) < (s : ℝ) := by exact_mod_cast (show (0:ℕ) < s by omega)
  -- take logarithms of the size constraint `(q n)^{8/9} ≤ 2 s q(n-1)`
  have h1 : Real.log ((q n : ℝ) ^ (8 / 9 : ℝ)) ≤ Real.log (2 * (s : ℝ) * (q (n - 1) : ℝ)) :=
    Real.log_le_log (Real.rpow_pos_of_pos ha _) hsQ8
  rw [Real.log_rpow ha] at h1
  have hmul : Real.log (2 * (s : ℝ) * (q (n - 1) : ℝ)) =
      Real.log 2 + Real.log (s : ℝ) + Real.log (q (n - 1) : ℝ) := by
    rw [show (2:ℝ) * (s:ℝ) * (q (n-1):ℝ) = (2 * (s:ℝ)) * (q (n-1):ℝ) by ring]
    rw [Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < 2 * (s:ℝ))) (ne_of_gt hQ),
        Real.log_mul (by norm_num) (ne_of_gt hsr)]
  rw [hmul] at h1
  -- `log s ≥ (8/9) log(q n) - log 2 - log(q(n-1))`
  have hlog_sr : (8 / 9 : ℝ) * Real.log (q n : ℝ) - Real.log 2 - Real.log (q (n - 1) : ℝ)
      ≤ Real.log (s : ℝ) := by linarith
  have hlog_a' : (1 / 9 : ℝ) * Real.log (q n : ℝ) ≤ (1 / 9 : ℝ) * ((b₀ + ε') * (q (n - 1) : ℝ)) :=
    mul_le_mul_of_nonneg_left hlogq (by norm_num)
  -- main logarithmic estimate
  have key : Real.log ((q n : ℝ) / (s : ℝ)) ≤
      (1 / 9 : ℝ) * ((b₀ + ε') * (q (n - 1) : ℝ)) + Real.log 2 + Real.log (q (n - 1) : ℝ) := by
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hsr)]
    linarith
  have h2 : (0:ℝ) < 2 / (q (n - 1) : ℝ) := by positivity
  calc
    2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
        = (2 / (q (n - 1) : ℝ)) * Real.log ((q n : ℝ) / (s : ℝ)) := by ring
    _ ≤ (2 / (q (n - 1) : ℝ)) * ((1 / 9 : ℝ) * ((b₀ + ε') * (q (n - 1) : ℝ)) + Real.log 2 + Real.log (q (n - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left key (le_of_lt h2)
    _ = (2 / 9) * (b₀ + ε') + 2 * Real.log 2 / (q (n - 1) : ℝ) + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ) := by
          field_simp

end Work.TMC16Core.Main
