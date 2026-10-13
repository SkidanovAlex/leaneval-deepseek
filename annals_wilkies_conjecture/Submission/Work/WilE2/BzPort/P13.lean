/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.idealOfVars_isMaximal` (piece 0).
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
import Submission.Work.WilE2.BzPort.P12

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.idealOfVars_isMaximal ====
section

namespace Commons.Algebra.MvPolynomial

/-- The ideal of variables of `MvPolynomial (Fin m) k` is the kernel of the constant coefficient
map. -/
lemma idealOfVars_eq_ker_constantCoeff {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [MvPolynomial.idealOfVars, RingHom.mem_ker, MvPolynomial.constantCoeff_eq,
    show Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k)
      = MvPolynomial.X '' (Set.univ : Set (Fin m)) from by ext; simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hc)
    exact hi (by simp)
  · intro h m' hm'
    have hm0 : m' ≠ 0 := by
      intro h0
      exact (MvPolynomial.mem_support_iff.mp hm') (by rw [h0]; exact h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

theorem idealOfVars_isMaximal {k : Type*} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)

end Commons.Algebra.MvPolynomial
end


