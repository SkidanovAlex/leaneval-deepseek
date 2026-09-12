import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_encode_decode_bounded

set_option linter.style.haveILetI false

namespace Commons.Algebra.MvPolynomial

/-- There are only finitely many polynomials in `r` variables over `ℤ` of total degree at most
`d` all of whose coefficients are bounded by `K₀` in absolute value. -/
theorem finite_bounded_polys (r d K₀ : ℕ) :
    Finite {E : MvPolynomial (Fin r) ℤ // E.totalDegree ≤ d ∧ ∀ μ, |E.coeff μ| ≤ (K₀ : ℤ)} := by
  classical
  obtain ⟨Code, inst, encode, decode, hdec, _⟩ := exists_encode_decode_bounded r d K₀
  haveI : Fintype Code := inst
  refine Finite.of_injective encode ?_
  intro a b hab
  have h1 := hdec a
  have h2 := hdec b
  rw [hab] at h1
  exact Subtype.ext (h1.symm.trans h2)

end Commons.Algebra.MvPolynomial
