import Submission.Notions
import Submission.Reduction
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Algebraic bridge: from polynomials to totally positive algebraic integers

This module connects the *output* of Smith's converse theorem (irreducible
monic integer polynomials `R` all of whose complex roots are positive real
numbers) to the *input* of `Submission.Reduction.lambda_SSS_le_of_family`
(totally positive algebraic integers with `trace β < c * degree β`).

For a monic irreducible `R ∈ ℤ[x]` and a root `β ∈ ℂ`, the minimal polynomial
of `β` over `ℚ` is the rational polynomial underlying `R` (Gauss lemma), so:

* `β` is an algebraic integer (`IsIntegral ℤ β`), with `degree β = natDegree R`;
* every conjugate of `β` — i.e. every complex root of `R` — is `> 0`, so
  `β` is totally positive;
* `trace β = rootSumComplex R` (sum of the complex roots of `R`); hence
  `trace β / degree β` equals the root mean `rootMeanReal R / natDegree R`.

A root mean bound `rootMeanReal R < c * natDegree R` therefore yields a root
`β` with `trace β < c * degree β` (comparison in the complex order).
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open AlgebraicIntegers
open scoped Real ENNReal

namespace Submission.AlgebraicBridge

open Submission.Notions

/-- Sum of a multiset of complex numbers all of which are real (imaginary part
zero) has imaginary part zero. -/
private lemma multiset_sum_im {m : Multiset ℂ} (hm : ∀ z ∈ m, z.im = 0) :
    (m.sum).im = 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : a.im = 0 := hm a (by simp)
      have hs : (s.sum).im = 0 := ih (fun z hz => hm z (by simp [hz]))
      simp [ha, hs]

/-- Evaluating a polynomial over ℚ at `z : ℂ` gives the same result as
evaluating the underlying integer polynomial at `z` (the ℚ-structure on `ℂ`
extends the ℤ-structure). -/
private lemma aeval_rat_eq_aeval_int (p : Polynomial ℤ) (z : ℂ) :
    Polynomial.aeval z (p.map (algebraMap ℤ ℚ)) = Polynomial.aeval z p := by
  exact (Polynomial.aeval_eq_aeval_map (R := ℤ) (S := ℂ) (T := ℚ)
    (φ := algebraMap ℤ ℚ) (by
      exact (IsScalarTower.algebraMap_eq ℤ ℚ ℂ).symm) p z).symm

/-- The algebraic bridge: from a monic irreducible integer polynomial all of
whose complex roots are positive real numbers and whose root sum is below
`c * natDegree`, extract a totally positive algebraic integer root with
`trace < c * degree`. -/
theorem bridge {R : Polynomial ℤ} (hmon : R.Monic) (hirr : Irreducible R)
    (hdeg : 1 ≤ R.natDegree) (hpos : ∀ z : ℂ, Polynomial.aeval z R = 0 → (0 : ℂ) < z) {c : ℝ}
    (hc : (rootSumComplex R).re < c * (R.natDegree : ℝ)) :
    ∃ β : ℂ, IsIntegral ℤ β ∧ IsTotallyPositive β ∧ trace β < (c : ℂ) * degree β := by
  -- `RQ` is the rational polynomial underlying `R`, `RC` its complex version.
  let RQ : Polynomial ℚ := R.map (algebraMap ℤ ℚ)
  let RC : Polynomial ℂ := R.map (algebraMap ℤ ℂ)
  -- By Gauss's lemma `RQ` is monic and irreducible over `ℚ`.
  have hRQ_mon : RQ.Monic := by
    simpa [RQ] using (hmon.map (algebraMap ℤ ℚ))
  have hRQ_irr : Irreducible RQ := by
    have hiff : Irreducible R ↔ Irreducible (R.map (algebraMap ℤ ℚ)) :=
      (hmon.irreducible_iff_irreducible_map_fraction_map (R := ℤ) (K := ℚ))
    simpa [RQ] using hiff.mp hirr
  -- `RC` is nonconstant, hence (ℂ algebraically closed) has a root `β`.
  have hRC_mon : RC.Monic := by
    simpa [RC] using (hmon.map (algebraMap ℤ ℂ))
  have hRC_natDegree : RC.natDegree = R.natDegree := by
    simpa [RC] using (hmon.natDegree_map (algebraMap ℤ ℂ))
  have hRC_deg_ne : RC.degree ≠ 0 := by
    have hnd : 0 < RC.natDegree := by
      rw [hRC_natDegree]
      exact lt_of_lt_of_le Nat.zero_lt_one hdeg
    exact ne_of_gt ((Polynomial.natDegree_pos_iff_degree_pos.mp hnd))
  obtain ⟨β, hβroot⟩ := IsAlgClosed.exists_root RC hRC_deg_ne
  have hβRC : Polynomial.eval β RC = 0 := by
    simpa [Polynomial.IsRoot] using hβroot
  have hβR : Polynomial.aeval β R = 0 := by
    rw [Polynomial.aeval_def]
    rw [Polynomial.eval₂_eq_eval_map]
    simpa [RC] using hβRC
  have hnatβ : Polynomial.aeval β RQ = Polynomial.aeval β R := by
    simpa [RQ] using (aeval_rat_eq_aeval_int R β)
  have hβRQ : Polynomial.aeval β RQ = 0 := by
    rw [hnatβ]
    exact hβR
  -- Minimal polynomial: since `RQ` is monic irreducible with root `β`,
  -- `minpoly ℚ β = RQ`.
  have hmin : minpoly ℚ β = RQ := by
    exact (minpoly.eq_of_irreducible_of_monic (A := ℚ) (x := β) hRQ_irr hβRQ hRQ_mon).symm
  have hdegβ : degree β = R.natDegree := by
    unfold degree
    rw [hmin]
    simpa [RQ] using (hmon.natDegree_map (algebraMap ℤ ℚ))
  have htraceβ : trace β = rootSumComplex R := by
    unfold trace
    rw [hmin, rootSumComplex]
  -- Every conjugate of `β` (root of `minpoly ℚ β`) is a complex root of `R`,
  -- hence positive by `hpos`.
  have hconj_pos : ∀ γ ∈ (minpoly ℚ β).aroots ℂ, 0 < γ := by
    intro γ hγ
    rw [hmin] at hγ
    have hγmem : RQ ≠ 0 ∧ Polynomial.aeval γ RQ = 0 := by
      exact (Polynomial.mem_aroots.mp hγ)
    have hnatγ : Polynomial.aeval γ RQ = Polynomial.aeval γ R := by
      simpa [RQ] using (aeval_rat_eq_aeval_int R γ)
    have hγR : Polynomial.aeval γ R = 0 := by
      rw [← hnatγ]
      exact hγmem.2
    exact hpos γ hγR
  refine ⟨β, ?_⟩
  constructor
  · exact ⟨R, hmon, hβR⟩
  · constructor
    · constructor
      · unfold IsAlgebraic
        refine ⟨RQ, ?_, hβRQ⟩
        exact hRQ_mon.ne_zero
      · exact hconj_pos
    · -- trace comparison: the trace is a real number, and its real part is
      -- bounded by `hc`; use the real-comparison criterion of `Reduction`.
      have htr_im : (trace β).im = 0 := by
        rw [htraceβ]
        unfold rootSumComplex
        apply multiset_sum_im
        intro z hz
        have hzmem : RQ ≠ 0 ∧ Polynomial.aeval z RQ = 0 := by
          exact (Polynomial.mem_aroots.mp hz)
        have hnatγ : Polynomial.aeval z RQ = Polynomial.aeval z R := by
          simpa [RQ] using (aeval_rat_eq_aeval_int R z)
        have hzR : Polynomial.aeval z R = 0 := by
          rw [← hnatγ]
          exact hzmem.2
        exact (Complex.pos_iff.mp (hpos z hzR)).2.symm
      have hre : (trace β).re < c * (degree β : ℝ) := by
        rw [htraceβ, hdegβ]
        exact hc
      exact (Submission.Reduction.trace_lt_mul_degree_iff htr_im).mpr hre

end Submission.AlgebraicBridge
