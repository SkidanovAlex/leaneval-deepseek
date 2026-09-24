import Mathlib
import Submission.Commons.NumberTheory.Sieve.sum_moebius_of_dvd_between

namespace Work.LinearSieve.Selberg

/-- The Möbius sum over the divisors of `l'` that are multiples of `l ∣ l'`:
since `l'` is squarefree, the only surviving term is `d = l'`, giving `μ l` when `l = l'` and `0`
otherwise. -/
theorem mu_sum_multiples (l l' : ℕ) (hl : l ∣ l') (hl' : l' ≠ 0) (hsq : Squarefree l') :
    ∑ d ∈ l'.divisors.filter (fun d => l ∣ d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)
      = if l = l' then ((ArithmeticFunction.moebius l : ℤ) : ℝ) else 0 := by
  have _hl' : l' ≠ 0 := hl'
  exact Commons.NumberTheory.Sieve.sum_moebius_of_dvd_between l l' hsq hl


end Work.LinearSieve.Selberg
