import Mathlib

namespace Work.FIArea7

lemma card_divisors_mul_primeFactors (m k : ℕ) (hm : 1 ≤ m) (hk1 : 1 ≤ k) (hsub : k.primeFactors ⊆ m.primeFactors) : (m * k).divisors.card = ∏ p ∈ m.primeFactors, (m.factorization p + k.factorization p + 1) := by
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  rw [Nat.card_divisors (by positivity), Nat.primeFactors_mul hm0 hk0, Finset.union_eq_left.mpr hsub]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [Nat.factorization_mul hm0 hk0, Finsupp.add_apply]

end Work.FIArea7
