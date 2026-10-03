import Mathlib

namespace Work.A3

/-- If `p` is prime, `p` does not divide `a`, and `p ^ ν` divides `a * c` (in `ℤ`), then the whole
of `p ^ ν` must divide `c`; consequently `gcd c.natAbs (p ^ ν) = p ^ ν`.  This is Euclid's lemma
iterated `ν` times, phrased with `Nat.gcd` so that it can be used on the additive/multiplicative
arithmetic side of Area A3. -/
lemma gcd_natAbs_prime_pow_eq_of_dvd_mul {p ν : ℕ} (hp : p.Prime) {a c : ℤ}
    (ha : ¬ ((p : ℤ) ∣ a)) (h : ((p : ℤ) ^ ν) ∣ a * c) :
    Nat.gcd c.natAbs (p ^ ν) = p ^ ν := by
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast]
    exact hp
  -- `p ^ ν` is coprime to `a`, since the prime `p` is.
  have hcop : IsCoprime ((p : ℤ) ^ ν) a := ((Prime.coprime_iff_not_dvd hpz).mpr ha).pow_left
  -- hence we may cancel `a` out of the divisibility `p ^ ν ∣ a * c`
  have h2 : ((p : ℤ) ^ ν) ∣ c := hcop.dvd_of_dvd_mul_left h
  -- transfer to `ℕ` via `natAbs`
  have h3 : p ^ ν ∣ c.natAbs := by
    have := (Int.natAbs_dvd_natAbs).mpr h2
    rwa [Int.natAbs_pow, Int.natAbs_natCast] at this
  exact Nat.gcd_eq_right h3

end Work.A3
