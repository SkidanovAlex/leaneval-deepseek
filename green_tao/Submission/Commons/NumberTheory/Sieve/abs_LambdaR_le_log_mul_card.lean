import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime

namespace Commons.NumberTheory.Sieve

/-- Termwise bound: for `d ∈ n.divisors` with `d ≤ R`, the `d`-th summand of `LambdaR R n`
is at most `log R` in absolute value. -/
private theorem abs_term_le_log {R n d : ℕ} (hR : 1 ≤ R) (hdvd : d ∈ n.divisors) (hdR : d ≤ R) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((R : ℝ) / (d : ℝ))| ≤ Real.log (R : ℝ) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdvd
  have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hrd_ge_one : 1 ≤ (R : ℝ) / (d : ℝ) :=
    (one_le_div hdposR).mpr (by exact_mod_cast hdR)
  have hrd_le : (R : ℝ) / (d : ℝ) ≤ (R : ℝ) := div_le_self hRpos.le (by exact_mod_cast hdpos)
  have hlog_nn : 0 ≤ Real.log ((R : ℝ) / (d : ℝ)) := Real.log_nonneg hrd_ge_one
  have hlog_le : Real.log ((R : ℝ) / (d : ℝ)) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by positivity) hrd_le
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  calc |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((R : ℝ) / (d : ℝ))|
      = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |Real.log ((R : ℝ) / (d : ℝ))| :=
        abs_mul _ _
    _ = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.log ((R : ℝ) / (d : ℝ)) := by
        rw [abs_of_nonneg hlog_nn]
    _ ≤ 1 * Real.log ((R : ℝ) / (d : ℝ)) := mul_le_mul_of_nonneg_right hmu hlog_nn
    _ = Real.log ((R : ℝ) / (d : ℝ)) := one_mul _
    _ ≤ Real.log (R : ℝ) := hlog_le

theorem abs_LambdaR_le_log_mul_card {R n : ℕ} (hR : 1 ≤ R) : |Commons.NumberTheory.Sieve.LambdaR R n| ≤ Real.log (R : ℝ) * ((n.divisors.filter (fun d => d ≤ R)).card : ℝ) := by
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  rw [LambdaR]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ d ∈ n.divisors.filter (fun d => d ≤ R),
        |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((R : ℝ) / (d : ℝ))|
      ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ R), Real.log (R : ℝ) :=
        Finset.sum_le_sum (fun d hd => by
          obtain ⟨hdvd, hdR⟩ := Finset.mem_filter.mp hd
          exact abs_term_le_log hR hdvd hdR)
    _ = Real.log (R : ℝ) * ((n.divisors.filter (fun d => d ≤ R)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Commons.NumberTheory.Sieve