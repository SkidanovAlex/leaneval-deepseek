import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

/-- If a prime power `p ^ (p.log m + 1)` still does not exceed `2 * m` -- i.e. the largest power
of `p` below `2 * m` lies strictly above `m` -- then `p` appears in the factorization of the
central binomial coefficient `choose (2 * m) m` with multiplicity at least one. -/
theorem choose_factorization_ge_one_of_pow_le (p m : ℕ) (hp : p.Prime)
    (h : p ^ (Nat.log p m + 1) ≤ 2 * m) :
    1 ≤ (Nat.choose (2 * m) m).factorization p := by
  let b := Nat.log p (2 * m) + 1
  have hb : Nat.log p (2 * m) < b := by
    simp [b]
  have hkm : m ≤ 2 * m := by omega
  have hsub : 2 * m - m = m := by omega
  -- Kummer's theorem, in the form of `Nat.factorization_choose`, expresses the exponent of
  -- `p` in `choose (2 * m) m` as a count of indices `i`.
  rw [Nat.factorization_choose hp hkm hb, hsub]
  -- It is enough to exhibit one index in the counted set: the index `Nat.log p m + 1`.
  rw [Finset.one_le_card]
  refine ⟨Nat.log p m + 1, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Ico]
  have hle : Nat.log p m + 1 ≤ Nat.log p (2 * m) :=
    Nat.le_log_of_pow_le hp.one_lt h
  constructor
  · constructor <;> omega
  · have hmlt : m < p ^ (Nat.log p m + 1) := by
      simpa using Nat.lt_pow_succ_log_self hp.one_lt m
    have hmod : m % p ^ (Nat.log p m + 1) = m := Nat.mod_eq_of_lt hmlt
    rw [hmod, ← two_mul]
    exact h

/-- For a prime `p`, the exponent of `p` in `lcmUpto (2 * m)` is bounded by the exponent in
`choose (2 * m) m` plus the exponent in `lcmUpto m`. -/
theorem log_choose_add_factorization (p m : ℕ) (hp : p.Prime) :
    Nat.log p (2 * m) ≤ (Nat.choose (2 * m) m).factorization p + Nat.log p m := by
  by_cases h : p ^ (Nat.log p m + 1) ≤ 2 * m
  · -- the largest power of `p` under `2 * m` is above `m`
    have hle1 : Nat.log p (2 * m) ≤ Nat.log p m + 1 := by
      have hm0 : m ≠ 0 := by
        have hpos : 0 < p ^ (Nat.log p m + 1) := pow_pos hp.pos _
        have h2m : 0 < 2 * m := lt_of_lt_of_le hpos h
        omega
      have hle_m : 2 * m ≤ m * p := by
        have hp2 : 2 ≤ p := hp.two_le
        calc
          2 * m ≤ p * m := Nat.mul_le_mul_right m hp2
          _ = m * p := by rw [Nat.mul_comm]
      exact (Nat.log_mono_right hle_m).trans_eq (Nat.log_mul_base hp.one_lt hm0)
    have hv : 1 ≤ (Nat.choose (2 * m) m).factorization p :=
      choose_factorization_ge_one_of_pow_le p m hp h
    omega
  · have hgt : 2 * m < p ^ (Nat.log p m + 1) := by omega
    have hlt : Nat.log p (2 * m) < Nat.log p m + 1 :=
      Nat.log_lt_of_lt_pow' (by omega : Nat.log p m + 1 ≠ 0) hgt
    omega

/-- The lcm of `{1, ..., 2*m}` divides the product of the central binomial coefficient
`choose (2 * m) m` and the lcm of `{1, ..., m}`. -/
theorem lcmUpto_even_dvd_binom_mul (m : ℕ) :
    Nat.lcmUpto (2 * m) ∣ Nat.choose (2 * m) m * Nat.lcmUpto m := by
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero (2 * m))
    (Nat.mul_ne_zero (Nat.choose_ne_zero (by omega : m ≤ 2 * m)) (Nat.lcmUpto_ne_zero m))]
  intro p hp
  rw [Nat.factorization_lcmUpto (2 * m) hp]
  rw [Nat.factorization_mul (Nat.choose_ne_zero (by omega : m ≤ 2 * m)) (Nat.lcmUpto_ne_zero m)]
  simp
  rw [Nat.factorization_lcmUpto m hp]
  exact log_choose_add_factorization p m hp

end Commons.NumberTheory.Chebyshev