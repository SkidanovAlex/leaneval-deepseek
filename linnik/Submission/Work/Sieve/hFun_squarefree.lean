import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs

namespace Work.Sieve

open Finset

/-- For a squarefree `n`, the totally multiplicative extension `hFun χ₁ n` collapses to the
product of `hPrime χ₁ p` over the prime factors of `n`: each local exponent is `1`. -/
theorem hFun_squarefree {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (n : ℕ) (hn : Squarefree n) :
    Work.LinnikAreas.Sieve.hFun χ₁ n = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.hPrime χ₁ p := by
  rw [Work.LinnikAreas.Sieve.hFun]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  rw [Nat.factorization_eq_one_of_squarefree hn hpp hpdvd, pow_one]

end Work.Sieve
