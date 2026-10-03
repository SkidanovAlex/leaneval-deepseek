/-
# `L²` membership of the Ionescu–Wainger symbol built from the dyadic circle bump

`Work.KMTPlan.A6.Decim.bump L = periodize (etaCut kmtEta (-(L:ℤ)))` is the circle bump of radius
`2^{-L}` around `0 ∈ ℝ/ℤ`.  Since `etaCut kmtEta (-(L:ℤ))` is measurable, bounded by `1` and
supported in `[-1,1]`, its periodisation is an `L^∞` function on the circle
(namely `Work.Analysis.IonescuWainger.memLp_periodize`), and so is every IW symbol obtained from
it by summing finitely many translates.  As the circle is a probability space, `L^∞` membership
implies `L²` membership, which is the statement of the target.

Nothing here uses `hL : 1 ≤ L`; the result is uniform in `L`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Decim.Defs
import Submission.Work.KMTPlan.A6.DecimComp.Defs
import Submission.Work.KMTPlan.A6.BandPieces
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.KMTAreas.A7Hi

open MeasureTheory

/-- The fixed KMT cutoff `η = Work.KMTContract.kmtEta` is measurable (it is a continuous
`ContDiffBump` composed with `ℝ → ℂ`). -/
theorem kmtEta_measurable : Measurable Work.KMTContract.kmtEta := by
  unfold Work.KMTContract.kmtEta
  exact Complex.continuous_ofReal.measurable.comp
    ((ContDiffBump.contDiff (n := 0) Work.KMTContract.kmtBump).continuous.measurable)

/-- The IW symbol over a finite set `A` of arithmetic frequencies of an `L^∞` symbol is again
`L^∞`: it is a finite sum of translates of the symbol, and Haar measure on the circle is
translation invariant. -/
theorem memLp_iwSymbolSet_top (A : Finset Work.Analysis.IonescuWainger.Circle)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (h : MemLp Φ ⊤ Work.Analysis.IonescuWainger.circleMeasure) :
    MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  have hterm : ∀ α : Work.Analysis.IonescuWainger.Circle,
      MemLp (fun ξ : Work.Analysis.IonescuWainger.Circle => Φ (ξ - α)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure := by
    intro α
    have hmp : MeasurePreserving
        (fun ξ : Work.Analysis.IonescuWainger.Circle => ξ + (-α))
        Work.Analysis.IonescuWainger.circleMeasure Work.Analysis.IonescuWainger.circleMeasure :=
      measurePreserving_add_right _ (-α)
    have := h.comp_measurePreserving hmp
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hsum : (∑ α ∈ A, fun ξ : Work.Analysis.IonescuWainger.Circle => Φ (ξ - α))
      = Work.Analysis.IonescuWainger.iwSymbolSet A Φ := by
    funext ξ
    simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  rw [← hsum]
  exact memLp_finsetSum' A (fun α _ => hterm α)

/-- The dyadic circle bump `bump L = periodize (etaCut kmtEta (-(L:ℤ)))` is in `L^∞(ℝ/ℤ)`: the
rescaled cutoff `θ ↦ η (2^L θ)` is measurable, bounded by `1`, and supported in `[-1,1]`, so only
finitely many translates contribute at any point of the circle. -/
theorem memLp_top_bump (L : ℕ) :
    MemLp (Work.KMTPlan.A6.Decim.bump L) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  unfold Work.KMTPlan.A6.Decim.bump
  refine Work.Analysis.IonescuWainger.memLp_periodize
    (φ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ)))
    ?_ (R := 1) (by norm_num) (C := 1) ?_ ?_
  · unfold Work.Analysis.IonescuWainger.etaCut
    exact kmtEta_measurable.comp (measurable_id.div_const _)
  · intro x hx
    rw [Work.Analysis.IonescuWainger.etaCut]
    apply Work.KMTContract.kmtEta_zero
    rw [abs_div]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(L : ℤ)) := zpow_pos (by norm_num) _
    rw [abs_of_pos hpos, le_div_iff₀ hpos, one_mul]
    have hc : (2 : ℝ) ^ (-(L : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    exact le_of_lt (lt_of_le_of_lt hc hx)
  · intro x
    rw [Work.Analysis.IonescuWainger.etaCut]
    exact Work.KMTContract.norm_kmtEta_le _

theorem memLp_two_iwSymbolSet_bump (A : Finset Work.Analysis.IonescuWainger.Circle) (L : ℕ) (hL : 1 ≤ L) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) 2
      Work.Analysis.IonescuWainger.circleMeasure :=
  (memLp_iwSymbolSet_top A (memLp_top_bump L)).mono_exponent (by norm_num)

end Work.KMTAreas.A7Hi
