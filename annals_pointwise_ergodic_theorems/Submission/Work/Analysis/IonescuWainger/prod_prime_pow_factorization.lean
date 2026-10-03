import Mathlib

namespace Work.Analysis.IonescuWainger

/-- The factorization of a product of prime powers `∏ p ∈ S, p ^ e p` at `q` is `e q` if `q ∈ S`
and `0` otherwise. -/
theorem prod_prime_pow_factorization {S : Finset ℕ} {e : ℕ → ℕ} (hp : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (S.prod (fun p => p ^ e p)).factorization q = if q ∈ S then e q else 0 := by
  classical
  -- every factor is a positive power of a prime, hence nonzero
  have hf : ∀ p ∈ S, p ^ e p ≠ 0 := fun p hpS => pow_ne_zero (e p) (hp p hpS).ne_zero
  -- push the factorization through the product
  calc (S.prod fun p => p ^ e p).factorization q
      = S.sum fun p => (p ^ e p).factorization q := Nat.factorization_prod_apply hf
    -- each prime power contributes a single `Finsupp` entry at the base prime
    _ = S.sum fun p => if p = q then e p else 0 :=
        Finset.sum_congr rfl fun p hpS => by
          rw [Nat.Prime.factorization_pow (hp p hpS), Finsupp.single_apply]
    -- all summands vanish except the (unique) one indexed by `q`
    _ = if q ∈ S then e q else 0 := Finset.sum_ite_eq' S q e

end Work.Analysis.IonescuWainger
