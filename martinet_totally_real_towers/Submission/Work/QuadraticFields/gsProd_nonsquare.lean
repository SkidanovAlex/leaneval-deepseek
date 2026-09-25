import Mathlib
import Submission.Work.QuadraticFields.CertificateReal

/-!
# The product `5 · 13 · 17 · 29 · 37 · 41 · 53` is not a rational square

`gsPrimes_prod` of `Work.QuadraticFields.CertificateReal` computes the discriminant of the totally
real quadratic certificate

  `F = ℚ(√(5·13·17·29·37·41·53))`

as the integer `2576450045`.  This file records the arithmetic fact that this integer is not a
square in `ℚ`, i.e. that `√(disc F)` is irrational, equivalently that `disc F` is not a square.

Note `2576450045 ≡ 5 (mod 8)`, so it is not even a square modulo `8`; but the cleanest formal proof
is by a prime-exact-division argument: the prime `5` divides `2576450045` exactly once.  An
integer that is a rational square and is divisible by a prime `p` exactly once would be a square
of an integer divisible by `p`, hence divisible by `p²` -- contradiction.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- **The discriminant of the real quadratic certificate is not a rational square.** -/
theorem gsProd_nonsquare : ∀ r : ℚ, r ^ 2 ≠ (2576450045 : ℚ) := by
  intro r hr
  -- A square in `ℚ` that equals an integer is the square of an integer.
  have h : r * r = ((2576450045 : ℤ) : ℚ) := by
    rw [← pow_two, hr]
    norm_num
  have hsq : IsSquare ((2576450045 : ℤ) : ℚ) := ⟨r, h.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨k, hk⟩ := hsq
  -- The prime `5` divides `2576450045` exactly once.
  have hp : Prime (5 : ℤ) := by norm_num
  have h1 : (5 : ℤ) ∣ 2576450045 := by norm_num
  have h2 : ¬ (5 : ℤ) ^ 2 ∣ 2576450045 := by norm_num
  have h5k : (5 : ℤ) ∣ k := by
    apply hp.dvd_of_dvd_pow (n := 2)
    rw [pow_two, ← hk]
    exact h1
  obtain ⟨c, hc⟩ := h5k
  apply h2
  rw [hk, hc]
  exact ⟨c * c, by ring⟩

end

end Work.QuadraticFields
