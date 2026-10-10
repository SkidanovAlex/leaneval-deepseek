import Mathlib
import Submission.Work.MotAS.AzDefs
import Submission.Work.MotAS.AzAux
import Submission.Work.MotAS.AzIrred.quadratic_irreducible
import Submission.Work.MotC5N3.azContent
import Submission.Work.MotC5N3.azDisc_not_square

/-!
# `Work.MotC5N3.azPrimeFwVec0` — the generic AS chart denominator `fwVecAS2 · 0` is prime

The `K`-generic (`K` an arbitrary field of characteristic `5`, in place of `RatFunc 𝕜`) form of
`Work.MotV5.ASLocal.azPrimeFwVec0`
(`Submission/Work/MotV5/ASLocal/azPrimeFwVec0.lean`, a fork of `Submission/Work/MotAS/azPrimeFwVec0.lean`).

The zeroth component `f̂₀ = fwVecAS2 a b g 0` of the forward chart map of the corrected AS chart is
the pullback under the chart map of the target hyperplane at infinity.  We show that it is a
**prime** element of `MvPolynomial (Fin 3) K` for arbitrary parameters `(a, b, g)` with
`azA a b = a² − ab − b² ≠ 0`, `a * b ≠ 0` and `g ≠ 0`.

The proof is the source proof with the base field generalised:

* `f̂₀ = C A · azQ a b g` with `A = azA a b` (`Work.MotAS.fwVecAS2_zero_eq`); since `A ≠ 0` the
  constant `C A` is a unit, so it suffices to prove `azQ a b g` irreducible;
* `azQ` is quadratic in `X₀` with coefficients `azC2, azC1, azC0` (`Work.MotAS.azQ_succEquiv`), so
  the general criterion `Work.MotAS.AzIrred.quadratic_irreducible` applies as soon as
  - `azC2 a b ≠ 0` (`Work.MotAS.azC2_ne_zero`),
  - the three coefficients have no common divisor (`Work.MotC5N3.azContent`,
    `Submission/Work/MotC5N3/azContent.lean` — forked from `Work.MotV5.ASLocal.azContent`), and
  - the discriminant is not a square (`Work.MotC5N3.azDisc_not_square`,
    `Submission/Work/MotC5N3/azDisc_not_square.lean` — forked from the two cases
    `Work.MotV5.ASLocal.azDisc_not_square_of_B_ne` and
    `Work.MotAS.AzDisc.azDisc_not_square_of_B_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.MotC5N3

open MvPolynomial

/-- **`azQ` is irreducible** over an arbitrary field `K` of characteristic `5`, by the quadratic
criterion applied to its `X₀`-quadratic form. -/
theorem azQ_irreducible (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.azA a b ≠ 0) (hg : g ≠ 0) :
    Irreducible (Work.MotAS.azQ a b g) := by
  rw [← MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2), Work.MotAS.azQ_succEquiv]
  refine Work.MotAS.AzIrred.quadratic_irreducible _ _ _ ?_ ?_ ?_
  · exact Work.MotAS.azC2_ne_zero a b hA
  · intro d h1 h2 h3
    exact Work.MotC5N3.azContent K a b g hA hg d h1 h2 h3
  · intro s
    simpa only [Work.MotAS.azDisc] using Work.MotC5N3.azDisc_not_square K a b g hA hg s

/-- **The AS chart denominator `fwVecAS2 a b g 0` is prime** over an arbitrary field `K` of
characteristic `5`. -/
theorem azPrimeFwVec0 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hA : Work.MotAS.azA a b ≠ 0) (hab : a * b ≠ 0) (hg : g ≠ 0) :
    Prime (Work.MotAS.fwVecAS2 a b g 0) := by
  rw [Work.MotAS.fwVecAS2_zero_eq]
  exact (Associated.irreducible_iff (associated_unit_mul_left (Work.MotAS.azQ a b g)
    (MvPolynomial.C (Work.MotAS.azA a b))
    (IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hA)))).mpr
    (azQ_irreducible K a b g hA hg) |>.prime

end Work.MotC5N3
