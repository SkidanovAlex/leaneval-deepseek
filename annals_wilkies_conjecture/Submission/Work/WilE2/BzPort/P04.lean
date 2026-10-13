/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Combinatorics.MvPolynomial.exists_polynomial_ncard_degree` (piece 0).
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
import Submission.Work.WilE2.BzPort.P03

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Combinatorics.MvPolynomial.exists_polynomial_ncard_degree ====
section

namespace Commons.Combinatorics.MvPolynomial

theorem exists_polynomial_ncard_degree {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : Polynomial ℚ, ∀ m : ℕ, (Set.ncard {c : Fin n →₀ ℕ | c.degree = m} : ℚ) = Q.eval (m : ℚ) := by
  refine ⟨Polynomial.C (((n - 1).factorial : ℚ))⁻¹ *
    (ascPochhammer ℚ (n - 1)).comp (Polynomial.X + 1), ?_⟩
  intro m
  have hcount : Set.ncard {c : Fin n →₀ ℕ | c.degree = m} = (n + m - 1).choose m := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {c : Fin n →₀ ℕ // c.degree = m} = (n + m - 1).choose m
    rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq (Fin n) m, Fintype.card_fin]
  rw [hcount, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have heval : (ascPochhammer ℚ (n - 1)).eval ((m : ℚ) + 1) =
      (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) := by
    rw [show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; ring]
    rw [ascPochhammer_nat_eq_natCast_ascFactorial]
    rw [← Nat.add_descFactorial_eq_ascFactorial' (m + 1) (n - 1)]
    rw [show (m + 1) + (n - 1) - 1 = m + n - 1 by omega]
  rw [heval]
  have hchoose : (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) =
      ((n - 1).factorial : ℚ) * ((m + n - 1).choose (n - 1) : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hchoose]
  have hsym : (m + n - 1).choose (n - 1) = (n + m - 1).choose m := by
    rw [Nat.add_comm n m]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hsym]
  have hne : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel_left₀ hne]

end Commons.Combinatorics.MvPolynomial
end


