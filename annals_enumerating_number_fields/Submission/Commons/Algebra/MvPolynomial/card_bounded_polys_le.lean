import Submission.Commons.Algebra.MvPolynomial.exists_encode_decode_bounded

namespace Commons.Algebra.MvPolynomial

/-- The number of polynomials in `r` variables over `ℤ` of total degree at most `d` all of
whose coefficients are bounded by `K₀` in absolute value is at most `(2 * K₀ + 2) ^ ((d + r).choose r)`.

This is the crude counting bound used to enumerate number fields: the exponent of the base `2 * K₀ + 2`
is the number `(d + r).choose r` of monomials of total degree at most `d` in `r` variables, and each
coefficient has at most `2 * K₀ + 1 ≤ 2 * K₀ + 2` possible values. -/
theorem card_bounded_polys_le (r d K₀ : ℕ) :
    Nat.card {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)}
      ≤ (2 * K₀ + 2) ^ ((d + r).choose r) := by
  obtain ⟨Code, inst, encode, decode, hdec, hbound⟩ := exists_encode_decode_bounded r d K₀
  have : Fintype Code := inst
  have hinj : Function.Injective encode := by
    intro a b hab
    exact Subtype.ext ((hdec a).symm.trans ((congrArg decode hab).trans (hdec b)))
  calc Nat.card {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)}
      ≤ Nat.card Code := Nat.card_le_card_of_injective encode hinj
    _ ≤ (2 * K₀ + 2) ^ ((d + r).choose r) := hbound

end Commons.Algebra.MvPolynomial
