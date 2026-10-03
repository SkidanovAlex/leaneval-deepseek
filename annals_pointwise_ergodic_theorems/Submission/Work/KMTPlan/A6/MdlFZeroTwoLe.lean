import Mathlib
import Submission.Work.KMTPlan.A6.LowLargeDefs
import Submission.Work.KMTPlan.A6.projVanishingF
import Submission.Work.KMTPlan.A6.eLpNorm_piExact_le
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# The `ℓ²` bound for the height-`0` model input `mdlF ρ u 0`

At arithmetic height `l = 0` the arithmetic frequency set of the Ionescu--Wainger analysis is the
singleton `(ℚ/ℤ)_{≤0} = {0}` (`Work.KMTAreas.A7.iwArithFreqs_zero`), so the height-`0` model input
is the plain periodised-cutoff Fourier multiplier

  `mdlF ρ u 0 f = Π_{0,≤-u} f = kmtProj ρ 0 (-(u : ℤ)) f
               = iwConv {0} (periodize (η(·/2^{-u}))) f`,

whose symbol `etSym (-(u : ℤ)) = periodize (etaCut kmtEta (-(u : ℤ)))` has sup norm at most `4`
throughout the window regime `-(u : ℤ) ≤ 1`: the cutoffs are supported in the arc of radius
`2^{-u} ≤ 1`, so at most four of their integer translates overlap
(`Work.KMTPlan.A6.norm_etSym_le_four`).  Consequently the `ℓ²` operator norm of `mdlF ρ u 0` is at
most `4`, *uniformly in the window* `2^{-u}` — this is `MdlFZeroTwoLe`, and it is what allows the
height-`0` slice of the low case of area A6 to be handled without any loss in the window.
-/

/-- The Ionescu--Wainger symbol with respect to the singleton frequency set `{0}` is the symbol
itself: `iwSymbolSet {0} Φ ξ = ∑_{α ∈ {0}} Φ (ξ - α) = Φ ξ`. -/
theorem iwSymbolSet_singleton_zero_KMT (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IonescuWainger.iwSymbolSet
      ({0} : Finset Work.Analysis.IonescuWainger.Circle) Φ = Φ := by
  funext ξ
  simp [Work.Analysis.IonescuWainger.iwSymbolSet]

/-- **The height-`0` model input is the periodised-cutoff multiplier.**  Unwrapping the
definitions, `mdlF ρ u 0 f = piExact (kmtPj ρ) 0 (-(u : ℤ)) f` is the height-`0`
Ionescu--Wainger projection `kmtProj ρ 0 (-(u : ℤ)) f`, i.e. the multiplier with symbol
`periodize (etaCut kmtEta (-(u : ℤ))) = etSym (-(u : ℤ))`. -/
theorem mdlF_zero_eq_iwConv (ρ : ℝ) (u : ℕ) (f : ℤ → ℂ) :
    mdlF ρ u 0 f
      = Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0) (etSym (-(u : ℤ))) f := by
  simp only [mdlF, Work.Analysis.EndVar.piExact, Work.KMTContract.kmtPj_proj,
    Work.KMTContract.kmtProj, etSym]
  split_ifs with h
  · rfl
  · exact absurd trivial h

/-- **The `ℓ²` bound for `mdlF ρ u 0`.**  The height-`0` exact-height shell with the narrow window
`2^{-u}`, `mdlF ρ u 0 f = Π_{0,≤-u} f`, satisfies `‖mdlF ρ u 0 f‖_{ℓ²(ℤ)} ≤ 4 ‖f‖_{ℓ²(ℤ)}` for
*every* window `u : ℕ`, the constant being independent of `u`. -/
theorem MdlFZeroTwoLe (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℕ) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlF ρ u 0 f) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  refine ⟨4, by norm_num, fun u f => ?_⟩
  rw [mdlF_zero_eq_iwConv]
  by_cases hf : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [hf]
    have htop : ENNReal.ofReal (4 : ℝ) * (⊤ : ℝ≥0∞) = ⊤ :=
      ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; norm_num)
    rw [htop]
    exact le_top
  · have hfmem : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hf)
    refine eLpNorm_iwConv_two_le_of_symbol_bound _ _ 4 (by norm_num) ?_ ?_ f hfmem
    · intro ξ
      rw [Work.KMTAreas.A7.iwArithFreqs_zero ρ, iwSymbolSet_singleton_zero_KMT]
      exact norm_etSym_le_four (-(u : ℤ)) (by omega) ξ
    · exact memLp_iwSym (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0) (-(u : ℤ))

end Work.KMTPlan.A6
