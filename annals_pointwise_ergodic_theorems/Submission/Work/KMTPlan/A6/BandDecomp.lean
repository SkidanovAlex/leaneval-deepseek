/-
# The frequency-band decomposition of the exact-height IW multiplier `Tm`

`Work.KMTAreas.A7.Tm ρ l φ f = iwConv (diffFreqs ρ l) (periodize φ) f` is the exact-height
Ionescu–Wainger multiplier with symbol `σ = iwSymbolSet (diffFreqs ρ l) (periodize φ)`.  Its
symbol is a sum of the single-frequency symbols `Φ (· - α)`, `α ∈ diffFreqs ρ l`, each of which is
supported near the arithmetic frequency `α`; when `Φ = periodize φ` is supported in a narrow arc
and the frequencies are separated, the resulting **bands** have pairwise disjoint spectra.

This file records the first, purely algebraic, layer of that decomposition: the symbol/operator
additivity over the finite set of frequencies, and the resulting identity

`Tm ρ l φ f = ∑_{α ∈ diffFreqs ρ l} (band at α) f`.

The analytic layer (the `L²`-orthogonality of the bands, `Work.KMTPlan.A6.sum_band_normSq_eq`,
and the shift–modulation estimate `Work.KMTPlan.A6.shift_modulation_le`) is built on top of it.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTPlan.A6.LowSmallSymDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal
open Work.Analysis.IonescuWainger

namespace Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The IW symbol over a finite frequency set is the sum of the single-frequency symbols. -/
theorem iwSymbolSet_eq_sum_singletons (S : Finset Circ) (Φ : Circ → ℂ) :
    iwSymbolSet S Φ = ∑ α ∈ S, iwSymbolSet {α} Φ := by
  funext ξ
  simp only [iwSymbolSet, Finset.sum_apply, Finset.sum_singleton]

/-- Evaluation form of `iwSymbolSet_eq_sum_singletons`. -/
theorem iwSymbolSet_singletons_apply (S : Finset Circ) (Φ : Circ → ℂ) (ξ : Circ) :
    iwSymbolSet S Φ ξ = ∑ α ∈ S, iwSymbolSet {α} Φ ξ := by
  have h := congrFun (iwSymbolSet_eq_sum_singletons S Φ) ξ
  simpa only [Finset.sum_apply] using h

/-- **Pointwise orthogonality of the bands.**  If `Φ` is supported in the arc `realArc K` and the
frequency set `S` is non-aliasing at scale `K`, then at every point `ξ` of the circle at most one
of the translated symbols `Φ (· - α)`, `α ∈ S`, is nonzero; hence
`‖∑_{α∈S} Φ(ξ-α)‖² = ∑_{α∈S} ‖Φ(ξ-α)‖²`. -/
theorem norm_iwSymbolSet_sq_eq_sum (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hsupp : SupportedInArc K Φ) (hNA : NonAliasing K S) (ξ : Circ) :
    ‖iwSymbolSet S Φ ξ‖ₑ ^ (2 : ℕ) = ∑ α ∈ S, ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ) := by
  classical
  set T : Finset Circ := S.filter (fun α => iwSymbolSet {α} Φ ξ ≠ 0) with hT
  have hmemT : T ⊆ S := by
    intro α hα
    exact (by simpa only [hT, Finset.mem_filter] using hα : α ∈ S ∧ _).1
  have hzero : ∀ α ∈ S, α ∉ T → iwSymbolSet {α} Φ ξ = 0 := by
    intro α hαS hαT
    by_contra hne
    exact hαT (by simp only [hT, Finset.mem_filter]; exact ⟨hαS, hne⟩)
  have hsub : ∀ a ∈ T, ∀ b ∈ T, a = b := by
    intro a ha b hb
    have haS : a ∈ S := hmemT ha
    have hbS : b ∈ S := hmemT hb
    have hane : iwSymbolSet {a} Φ ξ ≠ 0 :=
      (by simpa only [hT, Finset.mem_filter] using ha : a ∈ S ∧ _).2
    have hbne : iwSymbolSet {b} Φ ξ ≠ 0 :=
      (by simpa only [hT, Finset.mem_filter] using hb : b ∈ S ∧ _).2
    by_contra hne
    have hane' : Φ (ξ - a) ≠ 0 := by simpa [iwSymbolSet] using hane
    have hbne' : Φ (ξ - b) ≠ 0 := by simpa [iwSymbolSet] using hbne
    obtain ⟨θ, hθ, hθξ⟩ := hsupp (ξ - a) hane'
    obtain ⟨θ', hθ', hθ'ξ⟩ := hsupp (ξ - b) hbne'
    have heq : a + (θ : Circ) = b + (θ' : Circ) := by rw [hθξ, hθ'ξ]; abel
    exact hne (hNA a haS b hbS θ hθ θ' hθ' heq).1
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · rw [hT0] at hzero
    have hall : ∀ α ∈ S, iwSymbolSet {α} Φ ξ = 0 := fun α hα => hzero α hα (by simp)
    have hsym : iwSymbolSet S Φ ξ = 0 := by
      rw [iwSymbolSet_singletons_apply]; exact Finset.sum_eq_zero hall
    have hrhs : ∑ α ∈ S, ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ) = 0 :=
      Finset.sum_eq_zero (fun α hα => by rw [hall α hα]; simp)
    rw [hsym, hrhs]; simp
  · obtain ⟨α₀, hα₀⟩ := hTne
    have hsym : iwSymbolSet S Φ ξ = iwSymbolSet {α₀} Φ ξ := by
      rw [iwSymbolSet_singletons_apply]
      exact (Finset.sum_subset hmemT hzero).symm.trans
        (Finset.sum_eq_single α₀ (fun b hb hbne => absurd (hsub b hb α₀ hα₀) hbne)
          (fun h => absurd hα₀ h))
    have hrhs : ∑ α ∈ S, ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ)
        = ‖iwSymbolSet {α₀} Φ ξ‖ₑ ^ (2 : ℕ) :=
      (Finset.sum_subset hmemT (fun α hαS hαT => by rw [hzero α hαS hαT]; simp)).symm.trans
        (Finset.sum_eq_single α₀ (fun b hb hbne => absurd (hsub b hb α₀ hα₀) hbne)
          (fun h => absurd hα₀ h))
    rw [hsym, hrhs]

/-- **The `L²`-orthogonality (Plancherel) of the bands.**  Under the same hypotheses, the squared
`ℓ²` norms of the single-frequency pieces add up to the squared `ℓ²` norm of the full IW
multiplier: the bands have pairwise disjoint spectra. -/
theorem sum_band_normSq_eq (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hΦ : MemLp Φ ⊤ circleMeasure) (hsupp : SupportedInArc K Φ)
    (hNA : NonAliasing K S) (F : L2Z) :
    ∑ α ∈ S, (eLpNorm (⇑(iwOpSet {α} Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) 2 Measure.count) ^ (2 : ℕ)
      = (eLpNorm (⇑(iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 Measure.count) ^ (2 : ℕ) := by
  change ∑ α ∈ S, (eLpNorm (⇑(multiplierOf (iwSymbolSet {α} Φ)
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) 2 Measure.count) ^ (2 : ℕ)
      = (eLpNorm (⇑(multiplierOf (iwSymbolSet S Φ)
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 Measure.count) ^ (2 : ℕ)
  have hmeas : ∀ α ∈ S, AEMeasurable (fun ξ : Circ =>
      ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ) * ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ)) circleMeasure := by
    intro α _
    have h1 : AEMeasurable (fun ξ : Circ => ‖iwSymbolSet {α} Φ ξ‖ₑ) circleMeasure :=
      ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ).aestronglyMeasurable).aemeasurable.enorm
    have h2 : AEMeasurable (fun ξ : Circ => ‖(fourierZ F) ξ‖ₑ) circleMeasure :=
      (MeasureTheory.Lp.aestronglyMeasurable (fourierZ F)).aemeasurable.enorm
    exact (h1.pow_const 2).mul (h2.pow_const 2)
  calc ∑ α ∈ S, (eLpNorm (⇑(multiplierOf (iwSymbolSet {α} Φ)
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) 2 Measure.count) ^ (2 : ℕ)
      = ∑ α ∈ S, ∫⁻ ξ, ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ)
          * ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
        Finset.sum_congr rfl (fun α _ =>
          multiplierOfPlancherel (iwSymbolSet {α} Φ)
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)
    _ = ∫⁻ ξ, ∑ α ∈ S, (‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ)
          * ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ)) ∂circleMeasure :=
        (MeasureTheory.lintegral_finsetSum' S hmeas).symm
    _ = ∫⁻ ξ, (∑ α ∈ S, ‖iwSymbolSet {α} Φ ξ‖ₑ ^ (2 : ℕ))
          * ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ) ∂circleMeasure := by
        refine MeasureTheory.lintegral_congr (fun ξ => ?_)
        rw [Finset.sum_mul]
    _ = ∫⁻ ξ, ‖iwSymbolSet S Φ ξ‖ₑ ^ (2 : ℕ) * ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ)
          ∂circleMeasure := by
        refine MeasureTheory.lintegral_congr (fun ξ => ?_)
        rw [norm_iwSymbolSet_sq_eq_sum K S hsupp hNA ξ]
    _ = (eLpNorm (⇑(multiplierOf (iwSymbolSet S Φ)
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) 2 Measure.count) ^ (2 : ℕ) :=
        (multiplierOfPlancherel (iwSymbolSet S Φ)
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F).symm

end Work.KMTPlan.A6
