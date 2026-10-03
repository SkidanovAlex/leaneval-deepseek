import Mathlib

namespace Work.FIArea7.TwoCharPV

/-- A product of two coprime natural numbers is not a perfect square as soon as one of the factors
is not a perfect square.  Suggested proof: if `a * b = k^2` then for every prime `p`,
`v_p a + v_p b = 2·v_p k` while `v_p a = 0` or `v_p b = 0` (coprimality), so all exponents of `a`
are even and `a` is a square (`Nat.factorization_mul`, `Nat.factorization_pow`,
`Nat.prod_primeFactors_pow_factorization`, `Nat.Prime.not_coprime_iff_dvd`). -/
theorem nonsquare_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b)
    (ha : ∀ k : ℕ, a ≠ k ^ 2) : ∀ k : ℕ, a * b ≠ k ^ 2 := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  intro k hab
  -- If `a * b` were the square `k ^ 2`, then the prime exponents of `a` would all be even,
  -- making `a` a square, contradicting `ha`.
  have hsquare : IsSquare a := by
    rw [isSquare_iff_exists_sq]
    refine ⟨∏ p ∈ a.primeFactors, p ^ k.factorization p, ?_⟩
    calc a = ∏ p ∈ a.primeFactors, p ^ a.factorization p :=
            Nat.prod_primeFactors_pow_factorization ha0
      _ = ∏ p ∈ a.primeFactors, (p ^ k.factorization p) ^ 2 := by
            refine Finset.prod_congr rfl fun p hp => ?_
            have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
            -- `p ∣ a` and `Coprime a b` force `p ∤ b`
            have hpb : ¬ p ∣ b :=
              fun hpb => hp_prime.ne_one ((h.coprime_dvd_left hpa).eq_one_of_dvd hpb)
            -- comparing exponent of `p` in `a * b = k ^ 2`
            have h1 : a.factorization p + b.factorization p = 2 * k.factorization p := by
              rw [← Nat.factorization_mul_apply_of_coprime h, hab, Nat.factorization_pow,
                  Finsupp.smul_apply, nsmul_eq_mul]
              norm_num
            have hb0 : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpb
            have haf : a.factorization p = k.factorization p * 2 := by
              rw [hb0, add_zero] at h1
              rw [h1, Nat.mul_comm]
            rw [haf, ← pow_mul]
      _ = (∏ p ∈ a.primeFactors, p ^ k.factorization p) ^ 2 :=
            Finset.prod_pow a.primeFactors 2 (fun p => p ^ k.factorization p)
  obtain ⟨r, hr⟩ := hsquare
  exact ha r (by rw [hr, pow_two])

end Work.FIArea7.TwoCharPV
