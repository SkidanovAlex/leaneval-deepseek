import Mathlib.Data.Nat.Factorization.Basic

namespace Commons.Data.Nat

/-- The exponent of the prime `t` in the prime factorization of `p ^ k` is `k` if `p = t`
and `0` otherwise. -/
theorem factorization_prime_pow_apply {p t : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).factorization t = if p = t then k else 0 := by
  by_cases h : p = t
  · subst t
    rw [if_pos rfl]
    exact Nat.factorization_pow_self hp
  · rw [if_neg h]
    rw [Nat.factorization_eq_zero_iff]
    by_cases ht : t.Prime
    · right
      left
      intro hdvd
      have htp : t ∣ p := Nat.Prime.dvd_of_dvd_pow ht hdvd
      rcases (Nat.dvd_prime hp).mp htp with h1 | hteq
      · exact (Nat.Prime.ne_one ht) h1
      · exact h hteq.symm
    · left
      exact ht

end Commons.Data.Nat