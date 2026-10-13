/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Trdeg.trdeg_fractionRing_mvPolynomial` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P14

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Trdeg.trdeg_fractionRing_mvPolynomial ====
section

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
end


