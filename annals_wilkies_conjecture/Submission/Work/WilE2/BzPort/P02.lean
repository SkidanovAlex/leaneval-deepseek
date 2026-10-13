/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Combinatorics.Finset.sum_powerset_indicator` (piece 0).
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
import Submission.Work.WilE2.BzPort.P01

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Combinatorics.Finset.sum_powerset_indicator ====
section

namespace Commons.Combinatorics.Finset

/-- Rational version of `Finset.sum_powerset_neg_one_pow_card`: the alternating sum of
`(-1) ^ card` over the powerset of a finset equals `1` for the empty finset and `0` otherwise. -/
theorem sum_powerset_neg_one_pow_card_rat {α : Type*} [DecidableEq α] (x : Finset α) :
    (∑ m ∈ x.powerset, (-1 : ℚ) ^ m.card) = if x = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := x)
  have hcast : ((∑ m ∈ x.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℚ)
      = ∑ m ∈ x.powerset, (-1 : ℚ) ^ m.card := by
    push_cast
    rfl
  rw [← hcast, h]
  split_ifs <;> norm_num

theorem sum_powerset_indicator {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∑ T ∈ s.powerset, (-1 : ℚ) ^ T.card * (if ∀ i ∈ T, p i then (1 : ℚ) else 0) =
      (if ∀ i ∈ s, ¬ p i then (1 : ℚ) else 0) := by
  classical
  set A := s.filter p with hA
  have hAsub : A ⊆ s := by
    rw [hA]
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hpow : A.powerset = s.powerset.filter (· ⊆ A) := by
    ext T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans hAsub, h⟩, fun h => h.2⟩
  have hsum :
      (∑ T ∈ s.powerset, (-1 : ℚ) ^ T.card * (if ∀ i ∈ T, p i then (1 : ℚ) else 0))
        = ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card := by
    rw [hpow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    have hiff : (∀ i ∈ T, p i) ↔ T ⊆ A := by
      constructor
      · intro hp i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hT hi, hp i hi⟩
      · intro hTA i hi
        exact (Finset.mem_filter.mp (hTA hi)).2
    by_cases hTA : T ⊆ A
    · rw [if_pos (hiff.mpr hTA), if_pos hTA, mul_one]
    · rw [if_neg (fun h => hTA (hiff.mp h)), if_neg hTA, mul_zero]
  rw [hsum, sum_powerset_neg_one_pow_card_rat A]
  have hAempty : (∀ i ∈ s, ¬ p i) ↔ A = ∅ := by
    rw [hA]
    exact Finset.filter_eq_empty_iff.symm
  by_cases h : A = ∅
  · rw [if_pos h, if_pos (hAempty.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hAempty.mp hh))]

end Commons.Combinatorics.Finset
end


