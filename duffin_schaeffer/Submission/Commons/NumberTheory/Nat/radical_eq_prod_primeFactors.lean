import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Squarefree

/-!
# The radical of a natural number

Mathlib has no `Nat.radical`, so we introduce the (standard) radical of a
natural number, `radical N = ∏_{p | N} p`, the product of the distinct primes
dividing `N`, together with the characterizing equation
`radical N = ∏ p ∈ N.primeFactors, p` and a few basic properties.

This matches the local convention already used in the paper development
(`Submission/Vdw/CaseI.lean`, `Submission/Vdw/CaseIDisc.lean`), where `radical`
is *defined* as the product over the prime factors, so the characterizing
equation holds by `rfl`.
-/

namespace Commons.NumberTheory.Nat

/-- The **radical** of a natural number: the product of its distinct prime
factors, `∏_{p | N} p`.  This is the largest squarefree divisor of `N`; in
particular `radical 0 = 1` and `radical 1 = 1`. -/
noncomputable def radical (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, p

/-- The radical of `N` is the product over the prime factors of `N`. -/
theorem radical_eq_prod_primeFactors (N : ℕ) :
    radical N = ∏ p ∈ N.primeFactors, p := rfl

/-- The radical of a natural number is positive. -/
theorem radical_pos (N : ℕ) : 0 < radical N :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- The radical of a natural number is nonzero. -/
theorem radical_ne_zero (N : ℕ) : radical N ≠ 0 := (radical_pos N).ne'

/-- The radical of `N` divides `N`. -/
theorem radical_dvd (N : ℕ) : radical N ∣ N :=
  Nat.prod_primeFactors_dvd N

/-- For `N ≠ 0` the radical of `N` is at most `N`. -/
theorem radical_le_self {N : ℕ} (hN : N ≠ 0) : radical N ≤ N :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (radical_dvd N)

/-- `N` and its radical have the same prime factors. -/
theorem primeFactors_radical (N : ℕ) : (radical N).primeFactors = N.primeFactors :=
  Nat.primeFactors_prod_primeFactors N

/-- The radical of a natural number is squarefree. -/
theorem radical_squarefree (N : ℕ) : Squarefree (radical N) := by
  have hprod_ne : (∏ p ∈ N.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  change Squarefree (∏ p ∈ N.primeFactors, p)
  rw [Nat.squarefree_iff_factorization_le_one hprod_ne]
  intro q
  rw [Nat.factorization_prod_apply (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  have h1 : ∀ p ∈ N.primeFactors, p.factorization q = if p = q then (1 : ℕ) else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization, Finsupp.single_apply]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_ite_eq' N.primeFactors q (fun _ => 1)]
  split <;> norm_num

end Commons.NumberTheory.Nat