import Mathlib

namespace Work.DSM2p

/-- For a prime `p`, in any commutative ring the Frobenius difference
`(A - B) ^ p - (A ^ p - B ^ p)` is a multiple of `p`, hence lies in the ideal generated
by `(p : R)`.

Expanding `(A - B) ^ p` via Mathlib's `exists_add_pow_prime_eq` (which writes
`(x + y) ^ p = x ^ p + y ^ p + p * x * y * r`, the intermediate binomial coefficients
`p.choose k` being divisible by `p`) gives an explicit cofactor for the cross terms.
Applying the same lemma to `B + (-B) = 0` exhibits `B ^ p + (-B) ^ p` as a multiple of
`p`, which removes the sign ambiguity of the extremal term `(-B) ^ p`. -/
theorem N4e_sub_pow_sub_pow_mem {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime)
    (A B : R) :
    (A - B) ^ p - (A ^ p - B ^ p) ∈ Ideal.span {(p : R)} := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (R := R) hp A (-B)
  obtain ⟨r', hr'⟩ := exists_add_pow_prime_eq (R := R) hp B (-B)
  have h0 : (B + -B : R) ^ p = 0 := by rw [add_neg_cancel, zero_pow hp.ne_zero]
  rw [h0] at hr'
  have hsub : A + -B = A - B := by ring
  rw [hsub] at hr
  have key : (A - B) ^ p - (A ^ p - B ^ p) = (p : R) * (A * (-B) * r - B * (-B) * r') := by
    linear_combination hr - hr'
  rw [key, mul_comm]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton (p : R)))

end Work.DSM2p
