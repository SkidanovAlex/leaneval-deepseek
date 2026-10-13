/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right` (piece 0).
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
import Submission.Work.WilE2.BzPort.P06

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right ====
section

namespace Commons.Algebra.MvPolynomial

-- The graded-algebra structure on `MvPolynomial` induced by the total degree.  Mathlib
-- deliberately does not register it globally (one may want another grading), so we bring it
-- into scope locally for the proof below.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplying a polynomial `u` on the right by a homogeneous polynomial `g` of degree `a`
shifts the homogeneous decomposition by `a`: the `(j + a)`-th homogeneous component of `u * g`
is the `j`-th homogeneous component of `u` multiplied by `g`.

This is the `MvPolynomial` analogue of the graded-ring fact
`DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem homogeneousComponent_mul_of_isHomogeneous_right {σ K : Type*} [CommSemiring K]
    {g : MvPolynomial σ K} {a : ℕ} (hg : g.IsHomogeneous a) (u : MvPolynomial σ K) (j : ℕ) :
    MvPolynomial.homogeneousComponent (j + a) (u * g) = MvPolynomial.homogeneousComponent j u * g := by
  classical
  -- `homogeneousComponent` is the graded projection attached to the total-degree grading.
  have hbridge : ∀ (x : MvPolynomial σ K) (i : ℕ),
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) x) i : MvPolynomial σ K) =
        MvPolynomial.homogeneousComponent i x := by
    intro x i
    rw [← MvPolynomial.decomposition.decompose'_apply]
    rfl
  have hgmem : g ∈ MvPolynomial.homogeneousSubmodule σ K a := hg
  have key : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) (u * g)) (j + a) :
      MvPolynomial σ K) = (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) u j :
        MvPolynomial σ K) * g :=
    DirectSum.coe_decompose_mul_add_of_right_mem (MvPolynomial.homogeneousSubmodule σ K)
      (i := j) (j := a) hgmem
  rw [hbridge, hbridge] at key
  exact key

end Commons.Algebra.MvPolynomial
end


