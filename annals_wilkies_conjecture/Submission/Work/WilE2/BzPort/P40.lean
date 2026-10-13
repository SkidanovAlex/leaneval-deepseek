/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.height_idealOfVars` (piece 0).
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
import Submission.Work.WilE2.BzPort.P39

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.height_idealOfVars ====
section

namespace Commons.Algebra.MvPolynomial

theorem height_idealOfVars (n : ℕ) :
    (MvPolynomial.idealOfVars (Fin n) ℂ).height = (n : ℕ∞) := by
  haveI : (MvPolynomial.idealOfVars (Fin n) ℂ).IsPrime := by
    rw [← Commons.Algebra.MvPolynomial.ker_aeval_zero_eq_idealOfVars n]
    exact RingHom.ker_isPrime _
  refine le_antisymm ?_ ?_
  · have h := Ideal.height_le_ringKrullDim_of_isPrime
      (R := MvPolynomial (Fin n) ℂ) (I := MvPolynomial.idealOfVars (Fin n) ℂ)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add] at h
    simp only [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact WithBot.coe_le_coe.mp h
  · exact Commons.Algebra.MvPolynomial.idealOfVars_le_height _ le_rfl

end Commons.Algebra.MvPolynomial
end


