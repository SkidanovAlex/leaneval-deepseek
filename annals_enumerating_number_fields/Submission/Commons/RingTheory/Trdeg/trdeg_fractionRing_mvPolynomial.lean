import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Transcendence degree of the fraction field of a multivariate polynomial ring

For a field `K` and a natural number `s`, the field of fractions of the polynomial ring
`K[X₁, …, X_s]` has transcendence degree exactly `s` over `K`.  The variables already
form a transcendence basis of the polynomial ring, whose transcendence degree over `K`
is `s`, and passing to the fraction field adds only algebraic elements, so it does not
change the transcendence degree.
-/

namespace Commons.RingTheory.Trdeg

open Cardinal

/-- The transcendence degree over `K` of the fraction field of `MvPolynomial (Fin s) K` is `s`. -/
theorem trdeg_fractionRing_mvPolynomial (K : Type*) [Field K] (s : ℕ) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin s) K)) = (s : Cardinal) := by
  -- The fraction field of `K[X₁, …, X_s]` is a localization of it, hence algebraic over it.
  have hzero : Algebra.trdeg (MvPolynomial (Fin s) K)
      (FractionRing (MvPolynomial (Fin s) K)) = 0 :=
    @trdeg_eq_zero _ _ _ _ _
      (IsLocalization.isAlgebraic (FractionRing (MvPolynomial (Fin s) K))
        (nonZeroDivisors (MvPolynomial (Fin s) K)))
  -- Transcendence degree is additive in towers.
  have hadd := trdeg_add_eq K (MvPolynomial (Fin s) K)
    (A := FractionRing (MvPolynomial (Fin s) K))
  rw [hzero, add_zero] at hadd
  -- Reduce to the transcendence degree of the polynomial ring, which is `s`.
  rw [← hadd, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_mk_fin]

end Commons.RingTheory.Trdeg