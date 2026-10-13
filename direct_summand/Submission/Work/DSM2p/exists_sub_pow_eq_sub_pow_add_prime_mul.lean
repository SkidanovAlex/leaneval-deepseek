import Mathlib

namespace Work.DSM2p

/-- For a prime `p`, in any commutative ring `(x - y) ^ p` agrees with `x ^ p - y ^ p`
up to a multiple of `p`.

This is the `sub`-form of the Frobenius congruence modulo `p`: writing `(x - y) ^ p` as
`(x + (-y)) ^ p` and expanding with `exists_add_pow_prime_eq` leaves the two extremal
binomial terms `x ^ p` and `(-y) ^ p` plus an explicit multiple of `p`; applying the same
lemma to `y + (-y) = 0` exhibits `y ^ p + (-y) ^ p` as a multiple of `p`, which lets us
replace `(-y) ^ p` by `- y ^ p` modulo `p`. -/
theorem exists_sub_pow_eq_sub_pow_add_prime_mul {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    (x y : R) : ∃ t : R, (x - y) ^ p = x ^ p - y ^ p + (p : R) * t := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) hp x (-y)
  obtain ⟨r', hr'⟩ := exists_add_pow_prime_eq (R := R) hp y (-y)
  have h0 : (y + -y : R) ^ p = 0 := by rw [add_neg_cancel, zero_pow hp.ne_zero]
  rw [h0] at hr'
  refine ⟨y ^ 2 * r' - x * y * r, ?_⟩
  rw [sub_eq_add_neg, hr]
  linear_combination -hr'

end Work.DSM2p
