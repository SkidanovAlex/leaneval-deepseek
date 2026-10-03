import Mathlib.Data.Nat.Squarefree

namespace Commons.Data.Nat

open scoped BigOperators

/-- The number of squarefree divisors of a positive natural number `n` equals
`2` raised to the number of its distinct prime factors. -/
theorem card_squarefree_divisors (n : ℕ) (hn : n ≠ 0) :
    (((Nat.divisors n).filter (fun d : ℕ => Squarefree d)).card) =
      2 ^ (Nat.primeFactors n).card := by
  classical
  -- Mathlib identifies the (multi)set of squarefree divisors of `n` with the
  -- products of the elements of the subsets of the (normalized) prime factors of `n`.
  have hfs := Nat.divisors_filter_squarefree hn
  have hc := congrArg Multiset.card hfs
  simp only [Finset.card_val, Multiset.card_map] at hc
  rw [Finset.card_powerset] at hc
  -- For natural numbers the normalized factors are exactly the prime factors.
  rw [Nat.factors_eq] at hc
  simpa using hc

end Commons.Data.Nat