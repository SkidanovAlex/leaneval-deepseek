import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto

namespace Commons.NumberTheory.Moebius

theorem moebius_abs_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |ArithmeticFunction.moebius n| ≤ 1)

end Commons.NumberTheory.Moebius