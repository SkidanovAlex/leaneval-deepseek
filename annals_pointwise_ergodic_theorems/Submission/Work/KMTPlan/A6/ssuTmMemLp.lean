import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7

/-- **`ℓ²`-membership of the Ionescu--Wainger multiplier.**  If the IW symbol `iwSymbolSet A Φ`
of a finite arithmetic frequency set `A` and a symbol `Φ` is essentially bounded, then the
associated convolution/multiplier operator `iwConv A Φ` maps `ℓ²(ℤ)` into itself.  This is the
`q = 2` case of the Ionescu--Wainger multiplier theorem, in the form needed for `Tm`.

The proof realises `f ∈ ℓ²` as an element `F` of `lp (fun _ : ℤ => ℂ) 2`, uses that the `L^∞`
multiplier `iwOpSet A Φ h` with symbol `iwSymbolSet A Φ` is bounded on `ℓ²(ℤ)` with operator norm
at most `‖iwSymbolSet A Φ‖_∞ = (eLpNorm _ ⊤ circleMeasure).toReal`, and that on all of `ℓ²(ℤ)`
the convolution form `iwConv` agrees with the multiplier (`iwConvEqIwOpSetMemlp`). -/
theorem memLp_iwConv_of_memLp (A : Finset Circle) (Φ : Circle → ℂ)
    (hφ : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure)
    (f : ℤ → ℂ) (hf : MemLp f 2 Measure.count) :
    MemLp (iwConv A Φ f) 2 Measure.count := by
  have hfm : Memℓp f 2 := memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  set C : ℝ := (eLpNorm (iwSymbolSet A Φ) ⊤ circleMeasure).toReal with hCdef
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  have hCle : eLpNorm (iwSymbolSet A Φ) ⊤ circleMeasure ≤ ENNReal.ofReal C :=
    le_of_eq (ENNReal.ofReal_toReal hφ.eLpNorm_lt_top.ne).symm
  have hop : ‖iwOpSet A Φ hφ‖ ≤ C := norm_multiplierOf_le hφ hC0 hCle
  have hconv : ⇑(iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z)) = iwConv A Φ f :=
    (iwConvEqIwOpSetMemlp (A := A) (Φ := Φ) hφ (⟨f, hfm⟩ : L2Z)).symm
  have hmem : Memℓp (⇑(iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z))) 2 := (iwOpSet A Φ hφ _).property
  have hE : (⟨⇑(iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z)), hmem⟩ : L2Z)
      = iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z) := Subtype.ext rfl
  have hb : eLpNorm (iwConv A Φ f) 2 Measure.count
      ≤ ENNReal.ofReal C * eLpNorm f 2 Measure.count := by
    rw [← hconv, eLpNorm_two_count_eq_ofReal_lpNorm _ hmem, hE,
      eLpNorm_two_count_eq_ofReal_lpNorm f hfm]
    calc ENNReal.ofReal ‖iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z)‖
        ≤ ENNReal.ofReal (C * ‖(⟨f, hfm⟩ : L2Z)‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖iwOpSet A Φ hφ (⟨f, hfm⟩ : L2Z)‖
              ≤ ‖iwOpSet A Φ hφ‖ * ‖(⟨f, hfm⟩ : L2Z)‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ C * ‖(⟨f, hfm⟩ : L2Z)‖ := by gcongr
      _ = ENNReal.ofReal C * ENNReal.ofReal ‖(⟨f, hfm⟩ : L2Z)‖ := ENNReal.ofReal_mul hC0
  refine MeasureTheory.memLp_iff.mpr ?_
  exact lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

theorem ssuTmMemLp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ)
    (hΦ : MemLp (periodize φ) ⊤ circleMeasure)
    (hf : MemLp f 2 Measure.count) :
    MemLp (fun x : ℤ => Work.KMTAreas.A7.Tm ρ l φ f x) 2 Measure.count := by
  have hsym : MemLp (iwSymbolSet (diffFreqs ρ l) (periodize φ)) ⊤ circleMeasure :=
    memLp_iwSymbolSet (diffFreqs ρ l) hΦ
  have h := memLp_iwConv_of_memLp (diffFreqs ρ l) (periodize φ) hsym f hf
  simpa only [Work.KMTAreas.A7.Tm] using h

end Work.KMTPlan.A6
