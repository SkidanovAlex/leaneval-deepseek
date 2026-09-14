import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Real
set_option autoImplicit false

namespace Submission.TFacts

/-- log of a natural is nonnegative. -/
lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn)))

/-- t := 10 * (log n + 2) is ≥ 20 (hence positive) for every n. -/
lemma t_ge_twenty (n : ℕ) : 20 ≤ 10 * (Real.log (n : ℝ) + 2) := by
  nlinarith [log_nat_nonneg n]

/-- t is positive. -/
lemma t_pos (n : ℕ) : 0 < 10 * (Real.log (n : ℝ) + 2) := by
  linarith [t_ge_twenty n]

/-- 1/t ≤ 1/20. -/
lemma inv_t_le_inv_twenty (n : ℕ) : (10 * (Real.log (n : ℝ) + 2))⁻¹ ≤ (20 : ℝ)⁻¹ := by
  exact inv_le_inv₀ (by linarith [t_ge_twenty n]) (by norm_num) |>.mpr (t_ge_twenty n)

/-- log 1 = 0, so t = 20 at n = 1. -/
lemma t_eq_twenty_one : 10 * (Real.log (1 : ℝ) + 2) = 20 := by
  rw [Real.log_one]
  norm_num


/-- log is nondecreasing on naturals. -/
lemma log_le_log_of_le {m n : ℕ} (h : m ≤ n) : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  by_cases hm : m = 0
  · subst m
    norm_num [Real.log_zero]
    exact log_nat_nonneg n
  · have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    exact Real.log_le_log hmpos (by exact_mod_cast h : (m : ℝ) ≤ (n : ℝ))

/-- `t(d) := 10 (log d + 2)` is nondecreasing in `d`. -/
lemma t_mono {m n : ℕ} (h : m ≤ n) :
    10 * (Real.log (m : ℝ) + 2) ≤ 10 * (Real.log (n : ℝ) + 2) := by
  nlinarith [log_le_log_of_le h]

end Submission.TFacts
