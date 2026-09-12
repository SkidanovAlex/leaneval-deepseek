import Mathlib
import Submission.Commons.Analysis.MvPolynomial.homogeneousComponent_stable_of_stable_nonneg_full

/-!
# Stable multivariate polynomials: homogeneous components

Classical theorem (Borcea--Br\"and\'en--Liggett, JAMS 2009, Lemma 4.16, special case
`p = q = k`): every homogeneous component of a real stable polynomial with nonnegative
coefficients is stable (or zero).  Here "stable" means: either the polynomial is zero,
or it is nonvanishing at every point of the open upper half plane `UpperHalfPlane^n`.

The full proof (homogenisation `Σ a(α) z^α y^(d-|α|)`, followed by stability-preserving
operations: partial derivatives with respect to the homogenising variable and the
reciprocal operation) is developed in the module
`Submission.Commons.Analysis.MvPolynomial.homogeneousComponent_stable_of_stable_nonneg_full`
(lemma `Commons.Analysis.MvPolynomial.homogeneousComponent_stable_of_stable_nonneg_full`),
which this file imports and invokes.
-/

noncomputable section

open MvPolynomial

set_option autoImplicit false

namespace Commons.Analysis.MvPolynomial

/-- Classical theorem (Borcea-Braenden-Liggett, Lemma 4.16, JAMS 2009; special case
`p = q = k`): every homogeneous component of a real stable polynomial with nonnegative
coefficients is stable (or zero). Here "stable" means: either the polynomial is zero, or
it is nonvanishing at every point of the open upper half plane `UpperHalfPlane^n`.
Hint: BBL prove Lemma 4.16 via the homogenisation `sum a(alpha) z^alpha y^(d-|alpha|)`
(Theorem 4.5 of BBL: stable with nonnegative coefficients iff its homogenisation is stable),
followed by stability-preserving operations (partial derivative w.r.t. `y`, and the
reciprocal operation `y^q * z1^d * ... * zn^d * f(z1^(-1),...,zn^(-1),y^(-1))`). -/
theorem homogeneousComponent_stable_of_stable_nonneg (n k : ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    MvPolynomial.homogeneousComponent k p = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
          (MvPolynomial.homogeneousComponent k p) ≠ 0 := by
  exact homogeneousComponent_stable_of_stable_nonneg_full n k p hnn hstab

end Commons.Analysis.MvPolynomial
