/-
# The `ℓ²` bound for the IW multiplier from a pointwise bound on its symbol

The Ionescu–Wainger multiplier with symbol `m = iwSymbolSet A Φ` is the `ℓ²(ℤ)` Fourier
multiplier whose action on the Fourier side is multiplication by `m`; consequently its `ℓ²`
operator norm is at most the sup norm `‖m‖_∞` of the symbol.  This file records that implication
in the form needed by the §5 single-scale bookkeeping: if the symbol is pointwise bounded by `M`
on the whole circle, then

`‖iwConv A Φ f‖_{ℓ²(ℤ)} ≤ M ‖f‖_{ℓ²(ℤ)}` for *every* `f ∈ ℓ²(ℤ)`.

The two ingredients are

* `norm_multiplierOf_le` — the multiplier `iwOpSet A Φ h` has operator norm at most `M` when
  `‖iwSymbolSet A Φ‖_∞ ≤ M`, i.e. `eLpNorm (iwSymbolSet A Φ) ⊤ circleMeasure ≤ ofReal M`;
* `Work.KMTPlan.A6.iwConvEqIwOpSetMemlp` — on the whole of `ℓ²(ℤ)` (not merely on finitely
  supported sequences) the convolution form `iwConv` agrees with `iwOpSet`.

The passage from `eLpNorm` on the counting measure to the norm of `lp (fun _ : ℤ => ℂ) 2` is
`eLpNorm_two_count_eq_ofReal_lpNorm`, and `memlpOfMemLpCount` supplies the `Memℓp` instance for
an `L²` function on the counting measure.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal

namespace Work.KMTPlan.A6

open MeasureTheory
open Work.Analysis.IonescuWainger

/-- **The `ℓ²` operator norm of the IW multiplier is bounded by the sup norm of its symbol.**
If `‖iwSymbolSet A Φ ξ‖ ≤ M` for every `ξ` on the circle, then the Fourier multiplier with that
symbol has operator norm at most `M` on `ℓ²(ℤ)`. -/
theorem norm_iwOpSet_le_of_symbol_bound
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ ξ : Work.Analysis.IonescuWainger.Circle, ‖iwSymbolSet A Φ ξ‖ ≤ M)
    (hΦ : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure) :
    ‖iwOpSet A Φ hΦ‖ ≤ M := by
  have hC : eLpNorm (iwSymbolSet A Φ) ⊤ circleMeasure ≤ ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top (hf := by pw_aesm), eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le (ENNReal.ofReal M) (ae_of_all _ fun ξ => ?_)
    rw [ENNReal.ofReal, enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal M hM0]
    exact hM ξ
  exact norm_multiplierOf_le hΦ hM0 hC

theorem eLpNorm_iwConv_two_le_of_symbol_bound
    (A : Finset Work.Analysis.IonescuWainger.Circle) (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      ‖Work.Analysis.IonescuWainger.iwSymbolSet A Φ ξ‖ ≤ M)
    (hΦ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A Φ f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  -- The multiplier has operator norm at most `M` on `ℓ²(ℤ)`.
  have hop : ‖iwOpSet A Φ hΦ‖ ≤ M := norm_iwOpSet_le_of_symbol_bound A Φ M hM0 hM hΦ
  -- Realise `f ∈ ℓ²` as an element of `lp (fun _ : ℤ => ℂ) 2`.
  have hfm : Memℓp f 2 := memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  -- The convolution `iwConv` agrees with the multiplier `iwOpSet` on all of `ℓ²`.
  have hconv : ⇑(iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z)) = Work.Analysis.IWMultiplier.iwConv A Φ f :=
    (iwConvEqIwOpSetMemlp (A := A) (Φ := Φ) hΦ (⟨f, hfm⟩ : L2Z)).symm
  rw [← hconv]
  have hmem : Memℓp (⇑(iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z))) 2 :=
    (iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z)).property
  have e2 : (⟨⇑(iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z)), hmem⟩ : L2Z)
      = iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z) := Subtype.ext rfl
  rw [Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm _ hmem, e2,
    Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm f hfm]
  calc ENNReal.ofReal ‖iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z)‖
      ≤ ENNReal.ofReal (M * ‖(⟨f, hfm⟩ : L2Z)‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖iwOpSet A Φ hΦ (⟨f, hfm⟩ : L2Z)‖
            ≤ ‖iwOpSet A Φ hΦ‖ * ‖(⟨f, hfm⟩ : L2Z)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖(⟨f, hfm⟩ : L2Z)‖ := by gcongr
    _ = ENNReal.ofReal M * ENNReal.ofReal ‖(⟨f, hfm⟩ : L2Z)‖ := ENNReal.ofReal_mul hM0

end Work.KMTPlan.A6
