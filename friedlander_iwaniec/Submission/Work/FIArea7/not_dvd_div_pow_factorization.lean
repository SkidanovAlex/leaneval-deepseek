import Mathlib

namespace Work.FIArea7

/-- For `n ≠ 0` and a prime `p`, after dividing `n` by the exact power of `p`
dividing it, the quotient is no longer divisible by `p`. -/
lemma not_dvd_div_pow_factorization (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    ¬ p ∣ n / p ^ n.factorization p := by
  intro h
  set k := n.factorization p with hk
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp0
  -- `p ^ k` divides `n`, since the exponent of `p` in `p ^ k` is `k`
  have hdvd : p ^ k ∣ n := by
    rw [← Nat.factorization_le_iff_dvd hpk_ne hn, hp.factorization_pow]
    intro q
    by_cases hq : q = p
    · subst hq; simp [hk]
    · simp [Finsupp.single_eq_of_ne hq]
  -- if moreover `p ∣ n / p ^ k` then `p ^ (k+1) ∣ n`
  obtain ⟨c, hc⟩ := h
  have hdvd2 : p ^ (k + 1) ∣ n := by
    refine ⟨c, ?_⟩
    rw [← Nat.mul_div_cancel' hdvd, hc, pow_succ]
    ring
  -- but the exponent of `p` in `n` is exactly `k`, contradiction
  have hle : (p ^ (k + 1)).factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp0) hn).mpr hdvd2
  have h1 : (p ^ (k + 1)).factorization p = k + 1 := by
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  have h2 : n.factorization p = k := hk.symm
  have hpk1 : k + 1 ≤ k := by
    have := hle p
    rw [h1, h2] at this
    exact this
  omega

end Work.FIArea7
