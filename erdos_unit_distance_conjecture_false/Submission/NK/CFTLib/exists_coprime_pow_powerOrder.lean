import Mathlib

namespace NK.CFTLib

/-- The p-prime-to part `n / gcd(n, p^n)` of `n` is coprime to `p`.

Indeed `gcd(n, p^n)` carries, for every prime `q ∣ p`, the full `q`-adic valuation of `n`
(because `n ≤ n * v_q(p) = v_q(p^n)`), so dividing by it removes every prime factor of `p`
from `n` entirely. -/
lemma exists_coprime_pow_powerOrder_aux (n p : ℕ) (hn : n ≠ 0) :
    Nat.Coprime (n / Nat.gcd n (p ^ n)) p := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_pow hn, Nat.gcd_zero_right, Nat.div_self (Nat.pos_of_ne_zero hn)]
    exact Nat.coprime_one_left 0
  · have hg0 : Nat.gcd n (p ^ n) ≠ 0 := by
      intro h; exact absurd (Nat.gcd_eq_zero_iff.mp h).1 hn
    have hm0 : n / Nat.gcd n (p ^ n) ≠ 0 := by
      intro h
      have h1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left n (p ^ n))
      rw [h, mul_zero] at h1
      exact hn h1.symm
    rw [Nat.coprime_iff_gcd_eq_one]
    have hfac : (Nat.gcd (n / Nat.gcd n (p ^ n)) p).factorization = 0 := by
      rw [Nat.factorization_gcd hm0 hp]
      ext q
      rw [Finsupp.inf_apply, Finsupp.zero_apply]
      rcases eq_or_ne (p.factorization q) 0 with hp0 | hp0
      · simp [hp0]
      · have hqp : q.Prime := by
          by_contra h
          exact hp0 (Nat.factorization_eq_zero_of_not_prime p h)
        have hqdp : q ∣ p := Nat.dvd_of_factorization_pos hp0
        have hmf : (n / Nat.gcd n (p ^ n)).factorization q = 0 := by
          rw [Nat.factorization_div (Nat.gcd_dvd_left n (p ^ n)),
            Nat.factorization_gcd hn (pow_ne_zero n hp), Nat.factorization_pow]
          simp only [Finsupp.tsub_apply, Finsupp.inf_apply, Finsupp.smul_apply, smul_eq_mul]
          have h1 : 1 ≤ p.factorization q := (hqp.dvd_iff_one_le_factorization hp).mp hqdp
          have h2 : n.factorization q < n := Nat.factorization_lt q hn
          rw [inf_eq_left.mpr ((le_of_lt h2).trans (by simpa using Nat.mul_le_mul_left n h1)),
            Nat.sub_self]
        rw [hmf]
        simp
    have hg0' : Nat.gcd (n / Nat.gcd n (p ^ n)) p ≠ 0 := by
      intro h; exact absurd (Nat.gcd_eq_zero_iff.mp h).1 hm0
    rcases (Nat.factorization_eq_zero_iff' _).mp hfac with h | h
    · exact absurd h hg0'
    · exact h

theorem exists_coprime_pow_powerOrder (K : Type) [Field K] [NumberField K] (p : ℕ) :
    ∃ m : ℕ, Nat.Coprime m p ∧
      ∀ c : ClassGroup (NumberField.RingOfIntegers K), ∃ k : ℕ, (c ^ m) ^ (p ^ k) = 1 := by
  classical
  set n : ℕ := Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) with hn_def
  set g : ℕ := Nat.gcd n (p ^ n) with hg_def
  have hn : n ≠ 0 := by rw [hn_def]; exact Fintype.card_ne_zero
  have hcop : Nat.Coprime (n / g) p := by
    rw [hg_def]; exact exists_coprime_pow_powerOrder_aux n p hn
  refine ⟨n / g, hcop, ?_⟩
  intro c
  refine ⟨n, ?_⟩
  have hcn : c ^ n = 1 := by rw [hn_def]; exact pow_card_eq_one
  have hmul : g * (n / g) = n := by
    rw [hg_def]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left n (p ^ n))
  have hpw : p ^ n = g * (p ^ n / g) := by
    rw [hg_def]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right n (p ^ n))).symm
  have hcm : (c ^ (n / g)) ^ g = 1 := by
    rw [← pow_mul, mul_comm, hmul, hcn]
  rw [hpw, pow_mul, hcm, one_pow]

end NK.CFTLib
