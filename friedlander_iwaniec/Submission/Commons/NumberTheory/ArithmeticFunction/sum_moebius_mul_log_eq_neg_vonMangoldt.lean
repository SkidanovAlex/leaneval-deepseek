import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace Commons.NumberTheory.ArithmeticFunction

open Finset

set_option linter.unusedVariables false in
/-- Möbius inversion of the identity `∑_{d ∣ n} Λ d = log n`: summing the von Mangoldt
function weighted by the Möbius function over the divisors of `n` recovers `-Λ n`. -/
theorem sum_moebius_mul_log_eq_neg_vonMangoldt (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ))
      = -ArithmeticFunction.vonMangoldt n := by
  simpa only [ArithmeticFunction.log_apply] using
    ArithmeticFunction.sum_moebius_mul_log_eq (n := n)

end Commons.NumberTheory.ArithmeticFunction