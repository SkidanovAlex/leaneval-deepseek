import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpSet_zero_eq_self_of_band
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "CircB" => Work.BourgainPlan.IonescuWainger.Circle

/-- **The `ℓ²` `Tex`-output case of the band-limitation crux.**  If the profile `φ` is integrable
with summable Fourier coefficients `cw φ` and its periodisation is supported in the `δ`-arc around
`0`, then for every `f ∈ ℓ²` the exact-height projection `Tex ρ l φ f` is square summable and
band-limited to the union of the `δ`-arcs over the exact-height frequencies
`iwArithFreqsNew ρ l`.

This is the `ℓ²` half of the target's remaining gap (see
`NOTES_A7_fiberVarSamplingLargeLoss_SESSION10.md` §3b); the proof is the symbol computation
`𝓕(Tex ρ l φ f) = (Σ_{α∈A} periodize φ(·-α)) · 𝓕f`, whose symbol vanishes off the union. -/
theorem hasFreqSupport_Tex_of_memℓp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (δ : ℝ)
    (hm : MeasureTheory.Integrable φ)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hmsupp : ∀ θ : CircB, Work.Analysis.IonescuWainger.periodize φ θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∃ hw : Memℓp (Work.KMTAreas.A7.Tex ρ l φ f) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7.Tex ρ l φ f) hw
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
          Work.BourgainPlan.IonescuWainger.arcSet α δ) := by
  set A := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l with hA
  set σ : Circ → ℂ := Work.Analysis.IonescuWainger.iwSymbolSet A
    (Work.Analysis.IonescuWainger.periodize φ) with hσdef
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  have hsym : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hΨ
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨f, hf⟩ with hF
  set F' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize φ) hsym F
    with hF'
  have hweq : Work.KMTAreas.A7.Tex ρ l φ f = ⇑F' := by
    rw [← Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym F]
    rfl
  have hw : Memℓp (Work.KMTAreas.A7.Tex ρ l φ f) 2 := hweq ▸ F'.2
  refine ⟨hw, ?_⟩
  -- the Fourier transform of the multiplier is the product with the symbol
  have hft : Work.Analysis.IonescuWainger.fourierZ F'
      = hsym.toLp σ • Work.BourgainPlan.IonescuWainger.ftLp f hf := by
    rw [hF']
    exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf σ hsym F
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport]
  rw [show Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7.Tex ρ l φ f) hw
      = Work.BourgainPlan.IonescuWainger.ftLp (⇑F') F'.2 from
    Work.BourgainPlan.IonescuWainger.ftLp_congr hweq hw F'.2]
  filter_upwards [MeasureTheory.Lp.ext_iff.mp hft,
    MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      (hsym.toLp σ) (Work.BourgainPlan.IonescuWainger.ftLp f hf),
    MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hftξ hsmul hσeq hξ
  change (Work.Analysis.IonescuWainger.fourierZ F' : Circ → ℂ) ξ = 0
  rw [hftξ, hsmul]
  change ⇑(hsym.toLp σ) ξ • (Work.BourgainPlan.IonescuWainger.ftLp f hf : Circ → ℂ) ξ = 0
  have hzero : σ ξ = 0 := by
    refine iwSymbolSet_eq_zero_of_forall_not_mem_arcSet A φ δ hmsupp ξ ?_
    intro α hα hmem
    exact hξ (by simp only [Set.mem_iUnion]; exact ⟨α, hα, hmem⟩)
  rw [hσeq, hzero, zero_smul]

end Work.KMTAreas.A7
