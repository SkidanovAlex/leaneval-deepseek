import Mathlib
import Submission.Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Finset

/-- Namespace `Work.BMF.liouville`. Import: `Mathlib` and, for the last step,
`Submission.Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one`
(this module exists in the workspace and proves
`Summable (fun n : ℕ => Real.log (n:ℝ) / (n:ℝ)^2)` and `∑' n, Real.log (n:ℝ) / (n:ℝ)^2 ≤ 1`;
add that `import` line to the file).

`∑_{p ≤ M prime} log p / (p(p-1)) ≤ 2`: each term is `≤ 2 log p / p^2`, and the finite prime sum
is `≤ ∑'_n log n / n^2 ≤ 1`. -/
theorem primesLE_sum_log_div_mul_pred_le_two (M : ℕ) :
    ∑ p ∈ M.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 := by
  -- Each prime term is at most `2 log p / p ^ 2`.
  have hterm : ∀ p ∈ M.primesLE,
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
    intro p hp
    have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesLE hp
    have hpR2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hkey : (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    calc Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        = Real.log (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by ring
      _ ≤ Real.log (p : ℝ) * (2 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hkey hlog
      _ = 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by ring
  -- The summand `log n / n ^ 2` is nonnegative.
  have hnn : ∀ n : ℕ, 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      exact div_nonneg (Real.log_nonneg hn1) (by positivity)
  have hmain := Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one
  have hfin : ∑ p ∈ M.primesLE, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
    Summable.sum_le_tsum M.primesLE (fun i _ => hnn i) hmain.1
  calc ∑ p ∈ M.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ M.primesLE, 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 2 * ∑ p ∈ M.primesLE, Real.log (p : ℝ) / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 2 * ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ ≤ 2 := by linarith [hmain.2]

end Work.BMF.liouville
