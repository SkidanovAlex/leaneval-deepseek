import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

/-- The Frobenius difference `(x + y) ^ p - x ^ p - y ^ p` is a multiple of `p`; since `p`
lies in `Ideal.span {ϖ ^ p}`, so does the difference. Indeed, by the binomial theorem every
intermediate coefficient `p.choose k` (`0 < k < p`) is divisible by `p`, so
`(x + y) ^ p = x ^ p + y ^ p + p * x * y * r` for some `r`
(`exists_add_pow_prime_eq`), and the result follows from ideal closure under multiplication. -/
theorem sum_pow_sub_mem {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) (ϖ : R)
    (h : (p : R) ∈ Ideal.span {ϖ ^ p}) (x y : R) :
    (x + y) ^ p - x ^ p - y ^ p ∈ Ideal.span {ϖ ^ p} := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
  rw [hr]
  have key : x ^ p + y ^ p + p * x * y * r - x ^ p - y ^ p = (x * y * r) * (p : R) := by ring
  rw [key]
  exact Ideal.mul_mem_left _ _ h

end Work.DSM2p
