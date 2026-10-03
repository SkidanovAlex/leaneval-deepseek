import Mathlib
import Submission.Work.KMTPlan.A6.TleBandVarphiNtj

/-!
# Band-limitation of the exact-height multiplier `Tm`

`Work.KMTAreas.A7.Tm ρ l φ F = iwConv (diffFreqs ρ l) (periodize φ) F` is the Ionescu--Wainger
multiplier whose symbol is `Σ_{α ∈ diffFreqs ρ l} (periodize φ)(· - α)`, i.e. the multiplier
carrying the *exact height* frequency set `A_l \ A_{l-1}` rather than the whole arithmetic
frequency set `(ℚ/ℤ)_{≤l}`.

The band statement proved here is the exact analogue for `Tm` of
`Work.KMTPlan.A6.exists_hasFreqSupport_Tle_of_arc` (`TleBandVarphiNtj.lean`) for `Tle`
(`iwArithFreqs ρ l`), and the proof is the same: `Tm` is the scalar `L²`-multiplier whose symbol is
`iwSymbolSet (diffFreqs ρ l) (periodize φ)` (`iwConvEqIwOpSetMemlp`, valid on all of `ℓ²(ℤ)`),
whose Fourier transform is the product of the symbol with `𝓕F` (`fourierZ_multiplierOf`); the
symbol vanishes off the union of the `δ`-arcs because `periodize φ` does.  No boundedness of `F` and
no real-valuedness of the profile is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- If `ξ - α` lies in the arc `arcSet 0 δ` around `0`, then `ξ` lies in the translated arc
`arcSet α δ`. -/
private lemma mem_arcSet_of_sub_mem_tm {α ξ : Circ} {δ : ℝ}
    (h : ξ - α ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ) :
    ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet α δ := by
  obtain ⟨θ, hθ, hξ⟩ := h
  refine ⟨θ, hθ, ?_⟩
  have h2 : ξ = α + (0 + (θ : Circ)) := sub_eq_iff_eq_add'.mp hξ
  simpa using h2

theorem tmBandOfArc (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (δ : ℝ)
    (hper : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (harc : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (F : ℤ → ℂ) (hF : Memℓp F 2) :
    ∃ hw : Memℓp (Work.KMTAreas.A7.Tm ρ l φ F) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7.Tm ρ l φ F) hw
        (⋃ α ∈ Work.KMTAreas.A7.diffFreqs ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α δ) := by
  classical
  set A : Finset Circ := Work.KMTAreas.A7.diffFreqs ρ l with hA
  set σ : Circ → ℂ := Work.Analysis.IonescuWainger.iwSymbolSet A
    (Work.Analysis.IonescuWainger.periodize φ) with hσdef
  have hsym : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hper
  set Fl : Work.Analysis.IonescuWainger.L2Z := ⟨F, hF⟩ with hFldef
  set Fl' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize φ) hsym Fl
    with hFl'def
  have hweq : Work.KMTAreas.A7.Tm ρ l φ F = ⇑Fl' := by
    rw [← Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym Fl]
    rfl
  have hw : Memℓp (Work.KMTAreas.A7.Tm ρ l φ F) 2 := hweq ▸ Fl'.2
  refine ⟨hw, ?_⟩
  -- the Fourier transform of the multiplier is the product with its symbol
  have hft : Work.Analysis.IonescuWainger.fourierZ Fl'
      = hsym.toLp σ • Work.BourgainPlan.IonescuWainger.ftLp F hF := by
    rw [hFl'def]
    exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf σ hsym Fl
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  rw [show Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7.Tm ρ l φ F) hw
      = Work.BourgainPlan.IonescuWainger.ftLp (⇑Fl') Fl'.2 from
    Work.BourgainPlan.IonescuWainger.ftLp_congr hweq hw Fl'.2]
  filter_upwards [MeasureTheory.Lp.ext_iff.mp hft,
    MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (hsym.toLp σ) (Work.BourgainPlan.IonescuWainger.ftLp F hF),
    MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hftξ hsmul hσeq hξ
  change (Work.Analysis.IonescuWainger.fourierZ Fl' : Circ → ℂ) ξ = 0
  rw [hftξ, hsmul]
  change ⇑(hsym.toLp σ) ξ • (Work.BourgainPlan.IonescuWainger.ftLp F hF : Circ → ℂ) ξ = 0
  have hzero : σ ξ = 0 := by
    rw [hσdef, Work.Analysis.IonescuWainger.iwSymbolSet_apply]
    refine Finset.sum_eq_zero fun α hα => ?_
    by_contra hne
    have hsub : ξ - α ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := harc _ hne
    exact hξ (by
      simp only [Set.mem_iUnion]
      exact ⟨α, hα, mem_arcSet_of_sub_mem_tm hsub⟩)
  rw [hσeq, hzero, zero_smul]

end Work.KMTPlan.A6Clean
