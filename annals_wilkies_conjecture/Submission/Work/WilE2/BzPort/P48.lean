/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.KrullDimension.quotient_idealOfVars_eq_zero` (piece 0).
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
import Submission.Work.WilE2.BzPort.P47

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.KrullDimension.quotient_idealOfVars_eq_zero ====
section

namespace Commons.RingTheory.KrullDimension

/-- The quotient of `k[x₁,…,x_m]` by the ideal of the variables is the field `k`, so it has
Krull dimension zero. -/
theorem quotient_idealOfVars_eq_zero {k : Type*} [Field k] {m : ℕ} :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ MvPolynomial.idealOfVars (Fin m) k) = 0 := by
  have hmax : (MvPolynomial.idealOfVars (Fin m) k).IsMaximal :=
    Commons.Algebra.MvPolynomial.idealOfVars_isMaximal
  exact ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)

end Commons.RingTheory.KrullDimension
end


