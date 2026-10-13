/-
# Homogenization of an integer polynomial

For an integer polynomial `P` in `n` variables with `P.totalDegree ≤ d`, we homogenize it to
total degree `d` in `n + 1` variables by introducing a new variable `X 0`.  Evaluating the
homogenization at `(1, x_1, …, x_n)` recovers the evaluation of `P` at `x`.

The homogenization is the bridge that lets us apply Mathlib's height bound
`Height.mulHeight_eval_le` (which is stated for a family of *homogeneous* polynomials of a
common degree) to an arbitrary polynomial of bounded total degree.
-/

import Mathlib
import Submission.Work.WilkiesH.Defs

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace Work.WilkiesH.NT

variable {K : Type*} [Field K] {n : ℕ}

/-- The homogenization of `P : MvPolynomial (Fin n) ℤ` to total degree `d`, with respect to an
additional variable `X 0`.  The monomial `∏ i, X (i+1) ^ m i` of `P` is sent to the monomial
`X 0 ^ (d - m.degree) * ∏ i, X (i+1) ^ m i` of total degree `d`. -/
noncomputable def homog (P : MvPolynomial (Fin n) ℤ) (d : ℕ) : MvPolynomial (Fin (n + 1)) K :=
  ∑ m ∈ P.support,
    MvPolynomial.monomial (Finsupp.cons (d - m.degree) m) (((P.coeff m : ℤ) : K))

/-- `homog P d` together with the monomial `X 0 ^ d`, as a family of homogeneous polynomials of
degree `d` indexed by `Fin 2`, to which `Height.mulHeight_eval_le` can be applied. -/
noncomputable def homogFamily (P : MvPolynomial (Fin n) ℤ) (d : ℕ) :
    Fin 2 → MvPolynomial (Fin (n + 1)) K :=
  ![homog (K := K) P d, MvPolynomial.X 0 ^ d]

end Work.WilkiesH.NT
