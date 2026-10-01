import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.ZeroDensity.Jutila.LzAux.SigHalfLogAux

/-- For squarefree `n`, the cast of the product of the primes dividing `n` is the
product of the casts. -/
lemma self_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
  rw [← Nat.cast_prod (fun p => p) n.primeFactors]
  congr 1
  exact (Nat.prod_primeFactors_of_squarefree hn).symm

/-- For squarefree `n`, `κ(n) = ∏_{p | n} (p+1) ≥ ∏_{p|n} p = n`. -/
theorem kappa_ge_self {n : ℕ} (hn : Squarefree n) : (n : ℝ) ≤ Work.ZeroDensity.Jutila.kap n := by
  rw [self_eq_prod_primeFactors hn, Work.ZeroDensity.Jutila.kap]
  refine Finset.prod_le_prod₀ (fun p _ => ?_) (fun p hp => ?_)
  · exact_mod_cast Nat.zero_le p
  · have hp1 : (1 : ℝ) < (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).one_lt
      exact_mod_cast this
    linarith

end Work.ZeroDensity.Jutila.LzAux.SigHalfLogAux
