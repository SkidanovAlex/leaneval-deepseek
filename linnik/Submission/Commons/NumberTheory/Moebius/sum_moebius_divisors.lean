import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Moebius

namespace Commons.NumberTheory.Moebius

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, μ d) = if n = 1 then (1 : ℤ) else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := μ) (x := n)]
  rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rfl

end Commons.NumberTheory.Moebius