import Mathlib

namespace Work.WilG4a

/-- **Composition of a degree bound with a polynomial in its value.**

Given a "base" polynomial `B` in the two degree variables and a polynomial `c` in the value
of `B`, the composite function `(D, r) ↦ c (B(D, r))` is again the evaluation of a polynomial
in `D` and `r`, namely the substitution of `B` into `c`.

Concretely we exhibit `b` as the image of `c` under the `ℕ`-algebra homomorphism
`Polynomial ℕ →ₐ[ℕ] MvPolynomial (Fin 2) ℕ` sending `X` to `B` (i.e. `Polynomial.aeval B c`).
Instead of invoking the universal property, the proof inducts on `c` (closed under sums and
monomials), which keeps the construction purely explicit:
`monomial n a ↦ C a * B ^ n`.  The evaluation identity then follows from multiplicativity of
`MvPolynomial.eval` and `Polynomial.eval`. -/
theorem degree_poly_comp (B : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] b = Polynomial.eval (MvPolynomial.eval ![D, r] B) c := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨bp, hbp⟩ := hp
      obtain ⟨bq, hbq⟩ := hq
      exact ⟨bp + bq, fun D r => by
        rw [MvPolynomial.eval_add, hbp D r, hbq D r, Polynomial.eval_add]⟩
  | monomial n a =>
      exact ⟨MvPolynomial.C a * B ^ n, fun D r => by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
          Polynomial.eval_monomial]⟩

end Work.WilG4a
