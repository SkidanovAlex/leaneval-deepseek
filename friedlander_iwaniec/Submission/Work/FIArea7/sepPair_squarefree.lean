import Mathlib
import Submission.Work.FIArea7.SepDiv

namespace Work.FIArea7

/-- A product of an injective family of primes is squarefree: a strictly decreasing family of
primes has pairwise distinct values, hence pairwise coprime squarefree factors. -/
lemma squarefree_prod_of_strictAnti_prime {k : ℕ} (p : Fin k → ℕ)
    (hanti : StrictAnti p) (hprime : ∀ i, (p i).Prime) : Squarefree (∏ i, p i) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro i _ j _ hij
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hanti.injective h)))
  · intro i _
    exact (hprime i).prime.squarefree

/-- The separation product `d·m·n` of *FI* §24 is squarefree: it is the product of the (distinct)
primes in the decreasing enumeration `p` of its prime factors. -/
theorem sepPair_squarefree {r d m n : ℕ} (h : IsSepPair r d m n) : Squarefree (d * m * n) := by
  obtain ⟨k, p, hp, -, -, -⟩ := h
  obtain ⟨hanti, hprime, hprod⟩ := hp
  rw [hprod]
  exact squarefree_prod_of_strictAnti_prime p hanti hprime

end Work.FIArea7
