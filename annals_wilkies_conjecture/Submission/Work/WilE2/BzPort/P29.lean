/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.Polynomial.EventuallyPoly.partialSum` (piece 0).
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
import Submission.Work.WilE2.BzPort.P28

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.Polynomial.EventuallyPoly.partialSum ====
section

namespace Commons.Algebra.Polynomial.EventuallyPoly

open Finset

noncomputable section

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} s ^ n`. -/
def powSumPoly (n : ℕ) : _root_.Polynomial ℚ :=
  (_root_.Polynomial.bernoulli (n + 1) - _root_.Polynomial.C (_root_.bernoulli (n + 1))) *
    _root_.Polynomial.C (((n + 1 : ℕ) : ℚ)⁻¹)

lemma powSumPoly_eval (n t : ℕ) :
    (powSumPoly n).eval (t : ℚ) = ∑ s ∈ Finset.range t, (s : ℚ) ^ n := by
  unfold powSumPoly
  rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_sub, _root_.Polynomial.eval_C,
    _root_.Polynomial.eval_C, _root_.Polynomial.bernoulli_succ_eval]
  have hne : (((n : ℚ) + 1)) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} p.eval s`. -/
def sumPoly (p : _root_.Polynomial ℚ) : _root_.Polynomial ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), _root_.Polynomial.C (p.coeff i) * powSumPoly i

lemma sumPoly_eval (p : _root_.Polynomial ℚ) (t : ℕ) :
    (sumPoly p).eval (t : ℚ) = ∑ s ∈ Finset.range t, p.eval (s : ℚ) := by
  have h2 : (sumPoly p).eval (t : ℚ)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    rw [sumPoly, _root_.Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, powSumPoly_eval]
  have h1 : (∑ s ∈ Finset.range t, p.eval (s : ℚ))
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    simp_rw [_root_.Polynomial.eval_eq_sum_range]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [h2, ← h1]

end

theorem partialSum {f : ℕ → ℚ}
    (hf : ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t → f t = p.eval (t : ℚ)) :
    ∃ q : Polynomial ℚ, ∃ M : ℕ, ∀ t : ℕ, M ≤ t →
      (∑ s ∈ Finset.range t, f s) = q.eval (t : ℚ) := by
  obtain ⟨p, N, hfN⟩ := hf
  refine ⟨sumPoly p + Polynomial.C ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)),
    N, ?_⟩
  intro t ht
  rw [Polynomial.eval_add, Polynomial.eval_C]
  have hIcoF : ∑ s ∈ Finset.Ico N t, f s = ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Ico] at hs
    exact hfN s hs.1
  have hIcoP : ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ)
      = (∑ s ∈ Finset.range t, p.eval (s : ℚ))
        - (∑ s ∈ Finset.range N, p.eval (s : ℚ)) :=
    Finset.sum_Ico_eq_sub _ ht
  calc ∑ s ∈ Finset.range t, f s
      = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, f s := by
        rw [Finset.sum_range_add_sum_Ico f ht]
    _ = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by rw [hIcoF]
    _ = ∑ s ∈ Finset.range N, f s
          + ((∑ s ∈ Finset.range t, p.eval (s : ℚ))
              - (∑ s ∈ Finset.range N, p.eval (s : ℚ))) := by rw [hIcoP]
    _ = (sumPoly p).eval (t : ℚ)
          + ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)) := by
        rw [sumPoly_eval p t, sumPoly_eval p N]
        ring

end Commons.Algebra.Polynomial.EventuallyPoly
end


