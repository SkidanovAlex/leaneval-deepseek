/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.finrank_map_bot_mkQ_homogeneousSubmodule` (piece 0).
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
import Submission.Work.WilE2.BzPort.P18

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.finrank_map_bot_mkQ_homogeneousSubmodule ====
section

namespace Commons.Algebra.MvPolynomial

/-- The `t`-th graded piece of a polynomial ring in `m` variables has dimension
`(m + t - 1).choose t`, and its image under the quotient by the zero ideal (which
is an isomorphism onto the ring itself) has the same dimension. -/
theorem finrank_map_bot_mkQ_homogeneousSubmodule {k : Type*} [Field k] {m : ℕ} (t : ℕ) :
    Module.finrank k (Submodule.map ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) = (m + t - 1).choose t := by
  -- The quotient map by the zero ideal is a bijective `k`-linear map, hence a linear
  -- equivalence; mapping along it preserves the dimension.
  let f : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    (⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : (Submodule.Quotient.mk a : MvPolynomial (Fin m) k ⧸
        (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) =
        Submodule.Quotient.mk b := hab
    rw [Submodule.Quotient.eq] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective
      (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) y
    exact ⟨x, hx⟩
  let e : MvPolynomial (Fin m) k ≃ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : (e : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) = f :=
    rfl
  rw [← finrank_homogeneousSubmodule_eq_choose (k := k) m t]
  rw [show ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k) = f from rfl, ← he]
  rw [LinearEquiv.finrank_map_eq e]

end Commons.Algebra.MvPolynomial
end


