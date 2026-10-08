import Mathlib

namespace Work.FUS.AutFacts

/-- The totient of a power of two divides that power of two. -/
lemma totient_two_pow_dvd (k : ℕ) : Nat.totient (2 ^ k) ∣ 2 ^ k := by
  rcases k with _ | k
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
    have h : 2 ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    simpa using h

theorem mulAut_cyclic_eq_one_of_odd {A : Type*} [Group A] [Finite A] (hcyc : IsCyclic A) (k : ℕ)
    (hcard : Nat.card A = 2 ^ k) (β : A ≃* A) (hodd : Odd (orderOf β)) : β = 1 := by
  -- The order of `β` divides the order of the automorphism group,
  -- which is `Nat.totient (Nat.card A) = Nat.totient (2 ^ k)`.
  have hdvdAut : orderOf β ∣ Nat.card (MulAut A) := orderOf_dvd_natCard β
  rw [@IsCyclic.card_mulAut A _ _ hcyc, hcard] at hdvdAut
  -- hence it divides `2 ^ k`.
  have hdvd : orderOf β ∣ 2 ^ k := hdvdAut.trans (totient_two_pow_dvd k)
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  -- an odd power of two must be the zeroth power
  have hj : j = 0 := by
    by_contra hj
    exact (Nat.not_even_iff_odd.mpr (hjeq ▸ hodd)) (Even.pow_of_ne_zero even_two hj)
  have hone : orderOf β = 1 := by rw [hjeq, hj, pow_zero]
  exact orderOf_eq_one_iff.mp hone

end Work.FUS.AutFacts
