/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose` (piece 0).
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
import Submission.Work.WilE2.BzPort.P17

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose ====
section

namespace Commons.Algebra.MvPolynomial

theorem finrank_homogeneousSubmodule_eq_choose {k : Type*} [Field k] (n d : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin n) k d) = (n + d - 1).choose d := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hfin : Finite {e : Fin n →₀ ℕ | e.degree = d} :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) d).to_subtype
  have hft : Fintype {e : Fin n →₀ ℕ | e.degree = d} := Fintype.ofFinite _
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
    ({e : Fin n →₀ ℕ | e.degree = d})).finrank_eq]
  rw [Module.finrank_finsupp_self]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {e : Fin n →₀ ℕ // e.degree = d} = (n + d - 1).choose d
  rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq]
  simp only [Fintype.card_fin]

end Commons.Algebra.MvPolynomial
end


