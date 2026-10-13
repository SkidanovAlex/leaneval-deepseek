/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.minimalPrimes_homogeneous` (piece 0).
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
import Submission.Work.WilE2.BzPort.P24

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.minimalPrimes_homogeneous ====
section

namespace Commons.RingTheory.Ideal

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the standard `ℕ`-grading of a multivariate polynomial ring, the decomposition map
is the homogeneous component projection. -/
lemma decompose_eq_homogeneousComponent {k : Type*} [CommSemiring k] {m : ℕ}
    (x : MvPolynomial (Fin m) k) (j : ℕ) :
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin m) k) x j :
        MvPolynomial (Fin m) k) = MvPolynomial.homogeneousComponent j x := by
  rw [← DirectSum.Decomposition.decompose'_eq]
  exact MvPolynomial.decomposition.decompose'_apply x j

theorem minimalPrimes_homogeneous {k : Type*} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    {q : Ideal (MvPolynomial (Fin m) k)} (hq : q ∈ J.minimalPrimes) :
    ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q := by
  classical
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    intro i x hx
    rw [decompose_eq_homogeneousComponent]
    exact hJ x hx i
  have hqprime : q.IsPrime := hq.1.1
  have hcoreprime :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal.IsPrime :=
    hqprime.homogeneousCore
  have hJ_le_core :
      J ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal := by
    have hmono : J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) ≤
        q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
      Ideal.homogeneousCore_mono _ hq.1.2
    have hto : (J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤
        (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
      hmono
    rwa [Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self hJhom] at hto
  have hcore_le_q :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤ q :=
    Ideal.toIdeal_homogeneousCore_le _ q
  have hq_le_core :
      q ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
    hq.2 ⟨hcoreprime, hJ_le_core⟩ hcore_le_q
  have hqhom : q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
    (Ideal.IsHomogeneous.iff_eq _ q).mpr (le_antisymm hcore_le_q hq_le_core)
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hqhom x).mp hx j

end

end Commons.RingTheory.Ideal
end


