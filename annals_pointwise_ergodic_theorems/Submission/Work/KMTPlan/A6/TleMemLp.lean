import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTAreas.A7Hi.periodizeMemLpTop
import Submission.Work.Analysis.IWMultiplier.iwConv_singleton_eq_zero_of_not_integrable

namespace Work.KMTPlan.A6

open MeasureTheory

/-- **An Ionescu–Wainger multiplier with a bounded symbol preserves `ℓ²`.**

Let `A` be a finite set of frequencies on the circle and `Φ : Circle → ℂ` a symbol which is
pointwise bounded by `C`.  Then the multiplier `iwConv A Φ` — convolution with the Fourier
coefficients of the IW symbol `iwSymbolSet A Φ` — maps `ℓ²(ℤ)` to `ℓ²(ℤ)`.

The point of the statement is that **no measurability hypothesis on `Φ` is required**.  The proof
splits on whether the IW symbol `iwSymbolSet A Φ` is integrable on the circle:

* if it is, then it is a bounded measurable symbol, and the `ℓ²` multiplier theorem
  (`iwConvEqIwOpSetMemlp` + the operator norm bound on `iwOpSet`) applies;
* if it is not, then by Mathlib's convention for the Bochner integral
  (`MeasureTheory.integral_undef`) every Fourier coefficient of the symbol is the junk value `0`,
  so the convolution is the zero sequence (this is
  `Work.Analysis.IWMultiplier.iwKernel_eq_zero_of_not_integrable`). -/
theorem memlp_iwConv_two_of_bounded
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (C : ℝ)
    (hC : ∀ ξ : Work.Analysis.IonescuWainger.Circle, ‖Φ ξ‖ ≤ C)
    (F : ℤ → ℂ) (hF : Memℓp F 2) :
    Memℓp (Work.Analysis.IWMultiplier.iwConv A Φ F) 2 := by
  by_cases h : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Φ)
      Work.Analysis.IonescuWainger.circleMeasure
  · -- The symbol is integrable, hence (being bounded) an `L^∞` symbol: apply the `ℓ²` multiplier
    -- theorem.
    have hmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) ⊤
        Work.Analysis.IonescuWainger.circleMeasure :=
      MemLp.of_bound h.aestronglyMeasurable ((A.card : ℝ) * C)
        (ae_of_all _ (Work.Analysis.IonescuWainger.norm_iwSymbolSet_le A hC))
    have heq : Work.Analysis.IWMultiplier.iwConv A Φ F
        = ⇑(Work.Analysis.IonescuWainger.iwOpSet A Φ hmem
            (⟨F, hF⟩ : Work.Analysis.IonescuWainger.L2Z)) := by
      simpa using iwConvEqIwOpSetMemlp (A := A) (Φ := Φ) hmem
        (⟨F, hF⟩ : Work.Analysis.IonescuWainger.L2Z)
    rw [heq]
    exact (Work.Analysis.IonescuWainger.iwOpSet A Φ hmem
      (⟨F, hF⟩ : Work.Analysis.IonescuWainger.L2Z)).property
  · -- The symbol is not integrable: all Fourier coefficients are junk-zero, so the convolution
    -- vanishes.
    have hzero : Work.Analysis.IWMultiplier.iwConv A Φ F = 0 := by
      funext n
      rw [Work.Analysis.IWMultiplier.iwConv_apply]
      simp only [Work.Analysis.IWMultiplier.iwKernel_eq_zero_of_not_integrable h]
      simp
    rw [hzero]
    simp [Memℓp]

/-- **`Tle ρ l φ` preserves `ℓ²` whenever the periodisation of `φ` is bounded.**

This is the `Memℓp` form of the `ℓ²` bound for the linear Ionescu–Wainger multiplier
`T^{≤l}_φ = iwConv (iwArithFreqs ρ l) (periodize φ)`: the symbol `iwSymbolSet A (periodize φ)`
is bounded by `|A| M`, and (crucially, since only the *pointwise* bound `hM` is assumed, not
measurability of `φ` or of the periodisation) a bounded symbol always defines an `ℓ²`-bounded
multiplier, either by the `L²` multiplier theorem or because the multiplier is identically zero. -/
theorem TleMemLp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.periodize φ θ‖ ≤ M)
    (F : ℤ → ℂ) (hF : Memℓp F 2) :
    Memℓp (Work.KMTAreas.A7.Tle ρ l φ F) 2 := by
  simpa only [Work.KMTAreas.A7.Tle] using
    memlp_iwConv_two_of_bounded (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ) M hM F hF

end Work.KMTPlan.A6
