/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.homogeneous_isHomogeneous_mem_of_finite_quotient` (piece 0).
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
import Submission.Work.WilE2.BzPort.P34

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.homogeneous_isHomogeneous_mem_of_finite_quotient ====
section

namespace Commons.Algebra.MvPolynomial

theorem homogeneous_isHomogeneous_mem_of_finite_quotient {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : ∀ (j : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ p : MvPolynomial (Fin n) ℂ, p.IsHomogeneous j → p ∈ I := by
  obtain ⟨N, hN⟩ :=
    exists_pow_idealOfVars_le_of_homogeneousComponent_mem I hI hfin
  refine ⟨N, fun j hj p hp => ?_⟩
  apply hN
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  exact hp.coeff_eq_zero (by omega)

end Commons.Algebra.MvPolynomial

end


