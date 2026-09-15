import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

open scoped BigOperators

/-- The difference between the Chebyshev functions `ψ` and `θ` is exactly the sum of the von
Mangoldt function over all prime powers that are not themselves prime (i.e. over `n` with
`¬ n.Prime`), as the contributions of primes cancel: `Λ p = log p = θ`-term for prime `p`. -/
theorem psi_sub_theta_eq_sum_notPrime (x : ℝ) :
    Chebyshev.psi x - Chebyshev.theta x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
  -- Unfold the definitions of ψ and θ.
  change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) -
      (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log (p : ℝ)) =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n)
  -- Split the sum defining ψ into primes and non-primes.
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊)
      (p := fun n => n.Prime) (f := fun n => ArithmeticFunction.vonMangoldt n)]
  -- On primes, Λ p = log p, so the prime contribution to ψ coincides with θ.
  have hA : (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, ArithmeticFunction.vonMangoldt p) =
      (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2
  nlinarith

end Commons.NumberTheory.Chebyshev
