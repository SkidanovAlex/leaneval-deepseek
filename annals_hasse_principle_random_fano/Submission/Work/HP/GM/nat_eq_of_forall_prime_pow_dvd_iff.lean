import Mathlib

namespace Work.HP.GM

/-- If two naturals are divisible by exactly the same prime powers, then they are equal.
The hypothesis only concerns prime bases `p`; for a composite `p` the corresponding
exponents in `Nat.factorization` vanish, so the argument is driven by the primes. -/
theorem nat_eq_of_forall_prime_pow_dvd_iff {m n : ℕ}
    (H : ∀ p e : ℕ, p.Prime → (p ^ e ∣ m ↔ p ^ e ∣ n)) : m = n := by
  -- A number which is divisible by all prime powers of a nonzero number must be zero.
  have hzero : ∀ a b : ℕ, a = 0 → (∀ p e : ℕ, p.Prime → (p ^ e ∣ a ↔ p ^ e ∣ b)) → b = 0 := by
    intro a b ha H
    by_contra hb
    have hdiv : 2 ^ (b + 1) ∣ b := by
      rw [ha] at H
      exact (H 2 (b + 1) Nat.prime_two).mp (dvd_zero _)
    have hle : 2 ^ (b + 1) ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hdiv
    have hlt : b < 2 ^ (b + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ b))
    omega
  by_cases hm : m = 0
  · have hn : n = 0 := hzero m n hm H
    rw [hm, hn]
  by_cases hn : n = 0
  · have hm' : m = 0 := hzero n m hn (fun p e hp => (H p e hp).symm)
    rw [hm', hn]
  -- Now both are nonzero and we compare factorizations.
  apply Nat.dvd_antisymm
  · rw [← Nat.factorization_le_iff_dvd hm hn]
    intro p
    by_cases hp : p.Prime
    · have h1 : p ^ m.factorization p ∣ m := (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl
      exact (hp.pow_dvd_iff_le_factorization hn).mp ((H p (m.factorization p) hp).mp h1)
    · rw [Nat.factorization_eq_zero_of_not_prime m hp, Nat.factorization_eq_zero_of_not_prime n hp]
  · rw [← Nat.factorization_le_iff_dvd hn hm]
    intro p
    by_cases hp : p.Prime
    · have h1 : p ^ n.factorization p ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl
      exact (hp.pow_dvd_iff_le_factorization hm).mp ((H p (n.factorization p) hp).mpr h1)
    · rw [Nat.factorization_eq_zero_of_not_prime m hp, Nat.factorization_eq_zero_of_not_prime n hp]

end Work.HP.GM
