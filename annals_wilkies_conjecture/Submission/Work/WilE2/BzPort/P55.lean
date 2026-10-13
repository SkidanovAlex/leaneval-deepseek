/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.surjective_aeval_dehom` (piece 0).
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
import Submission.Work.WilE2.BzPort.P54

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.surjective_aeval_dehom ====
section

namespace Commons.Algebra.MvPolynomial

theorem surjective_aeval_dehom {k : Type*} [Field k] (r : ℕ) :
    Function.Surjective (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) :
      MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k) := by
  intro p
  refine ⟨MvPolynomial.rename Fin.succ p, ?_⟩
  rw [MvPolynomial.aeval_rename]
  have h : (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) ∘ Fin.succ
        = fun j : Fin r => MvPolynomial.X j := by
    funext j
    simp [Function.comp_apply]
  rw [h]
  exact MvPolynomial.aeval_X_left_apply p

end Commons.Algebra.MvPolynomial
end


