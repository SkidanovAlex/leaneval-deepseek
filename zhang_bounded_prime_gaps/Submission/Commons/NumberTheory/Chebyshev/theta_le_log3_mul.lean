import Mathlib.NumberTheory.Chebyshev
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_le_three_pow
import Submission.Commons.NumberTheory.Chebyshev.sum_Icc_prime_log_eq_theta_sub

namespace Commons.NumberTheory.Chebyshev

theorem theta_le_log3_mul (n : ℕ) :
    Chebyshev.theta (n : ℝ) ≤ Real.log 3 * (n : ℝ) := by
  calc
    Chebyshev.theta (n : ℝ) ≤ Chebyshev.psi (n : ℝ) := Chebyshev.theta_le_psi _
    _ = Real.log ((Nat.lcmUpto n : ℕ) : ℝ) := by
        rw [Chebyshev.psi_eq_log_lcmUpto n]
    _ ≤ Real.log (((3 ^ n : ℕ) : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.lcmUpto_pos n)
        · exact_mod_cast (lcmUpto_le_three_pow n)
    _ = Real.log 3 * (n : ℝ) := by
        rw [show (((3 ^ n : ℕ) : ℕ) : ℝ) = (3 : ℝ) ^ n by norm_num]
        rw [Real.log_pow]
        ring

end Commons.NumberTheory.Chebyshev
