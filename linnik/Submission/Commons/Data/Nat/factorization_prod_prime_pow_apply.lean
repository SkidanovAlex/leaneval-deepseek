import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Factorization.Basic

open scoped BigOperators

namespace Commons.Data.Nat

theorem factorization_prod_prime_pow_apply (S : Finset ℕ) (e : ℕ → ℕ)
    (hpr : ∀ p ∈ S, p.Prime) (t : ℕ) :
    ((∏ p ∈ S, p ^ e p).factorization) t = if t ∈ S then e t else 0 := by
  classical
  have hne : ∀ p ∈ S, p ^ e p ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ (hpr p hp).ne_zero
  calc
    ((∏ p ∈ S, p ^ e p).factorization) t = (S.prod fun p => p ^ e p).factorization t := rfl
    _ = ∑ p ∈ S, (p ^ e p).factorization t := by
      rw [Nat.factorization_prod_apply hne]
    _ = ∑ p ∈ S, if p = t then e p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.Prime.factorization_pow (hpr p hp), Finsupp.single_apply]
    _ = if t ∈ S then e t else 0 := by
      rw [Finset.sum_ite_eq']

end Commons.Data.Nat