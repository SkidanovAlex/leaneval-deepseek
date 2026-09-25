import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped lp BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

/-- **The modulation identity at the level of the `L²(𝕋)`-multiplier**: conjugating the
multiplier with symbol `Φ ∈ L^∞(𝕋)` by the translation `shiftLp α` of `L²(𝕋)` is the multiplier
with the translated symbol `mstArcTransLp α Φ = ξ ↦ Φ (ξ - α)`:
`Φ • shiftLp α F = shiftLp α ((mstArcTransLp α Φ) • F)`.

Pointwise, the left-hand side is the class `ξ ↦ Φ(ξ) · F(ξ + α)`, while the right-hand side is
`ξ ↦ (mstArcTransLp α Φ)(ξ + α) · F(ξ + α)` with `(mstArcTransLp α Φ)(ξ + α) = Φ(ξ)` a.e.; the
proof is the `L²` comparison of those two representatives. -/
theorem opMul_shiftLp (Φ : Lp ℂ ⊤ mstHaar) (α : mstCirc) (F : Lp ℂ 2 mstHaar) :
    Φ • shiftLp α F = shiftLp α ((mstArcTransLp α Φ) • F) := by
  refine Lp.ext ?_
  have hmp : MeasurePreserving (fun x : mstCirc => x + α) mstHaar mstHaar :=
    measurePreserving_add_right _ α
  have e1 : ((Φ • shiftLp α F : Lp ℂ 2 mstHaar) : mstCirc → ℂ)
      =ᵐ[mstHaar] fun ξ => (Φ : mstCirc → ℂ) ξ * (shiftLp α F : mstCirc → ℂ) ξ :=
    Lp.coeFn_lpSMul Φ (shiftLp α F)
  have e2 : ((shiftLp α (((mstArcTransLp α Φ) • F) : Lp ℂ 2 mstHaar) : Lp ℂ 2 mstHaar)
        : mstCirc → ℂ)
      =ᵐ[mstHaar] fun ξ => (((mstArcTransLp α Φ) • F : Lp ℂ 2 mstHaar) : mstCirc → ℂ) (ξ + α) :=
    shiftLp_coeFn α _
  have e3 : ((((mstArcTransLp α Φ) • F) : Lp ℂ 2 mstHaar) : mstCirc → ℂ)
      =ᵐ[mstHaar] fun ξ => (mstArcTransLp α Φ : mstCirc → ℂ) ξ * (F : mstCirc → ℂ) ξ :=
    Lp.coeFn_lpSMul (mstArcTransLp α Φ) F
  have e4 : ((shiftLp α F : Lp ℂ 2 mstHaar) : mstCirc → ℂ)
      =ᵐ[mstHaar] fun ξ => (F : mstCirc → ℂ) (ξ + α) :=
    shiftLp_coeFn α F
  have e5 : ((mstArcTransLp α Φ : Lp ℂ ⊤ mstHaar) : mstCirc → ℂ)
      =ᵐ[mstHaar] arcTranslate α (Φ : mstCirc → ℂ) :=
    mstArcTransLp_coeFn α Φ
  filter_upwards [e1, e2, hmp.quasiMeasurePreserving.ae e3, e4, hmp.quasiMeasurePreserving.ae e5]
    with ξ h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, arcTranslate_apply]
  rw [show (ξ + α) - α = ξ from by abel]

/-- **The modulation identity for the `ℓ²(ℤ)`-multiplier `opMul`.**  Multiplying the input by the character `m ↦ e^{2πi m α}` (`modSeq ρ α`) and then applying the multiplier with symbol `Φ` is the same as applying the multiplier with the *translated* symbol `ξ ↦ Φ (ξ - α)` and then modulating the output by `e^{2πi n α}`; equivalently, at every index `y`,
`opMul Φ (modSeq ρ α) _ y = fourier y α * opMul (arcTranslate α Φ) _ ρ _ y`.
This is the general-symbol form of `Work.BourgainPlan.IonescuWainger.opArc_arcShift` (which treats the arc symbols `Σ_{β∈E} φ(·-β)`); the general form is what the MST §4.3 freezing estimate needs, because there the symbol of the level-`s` model is the single profile-times-bump symbol `Φ_{2^n}ψ_s`.
Route: `ftLp_injective` + `ftLp_modSeq` (`ftLp (modSeq ρ α) = shiftLp α (ftLp ρ)`) + `ftLp_opMul`; the two sides are `L²(𝕋)` classes whose values at `ξ` are `Φ(ξ)·𝓕ρ(ξ+α)` and `(Φ(ξ+α-α))·𝓕ρ(ξ+α)`, equal because the representative of `mstArcTransLp α Φ` is a.e. `ξ ↦ Φ(ξ-α)` (`mstArcTransLp_coeFn`), shifted by `α` (use `MeasurePreserving (· + α)` and `shiftLp_coeFn`).  Alternatively: copy the proof of `opArc_arcShift` with the arc set `{0}` and `φ := (Φ : Circle → ℂ)`, using `arcShift`/`arcSymbolLp_coeFn` and `opMul_congr_ae` (`mstFreezeDefs.lean` has the coeFn lemmas). -/
theorem opMul_modSeq (Φ : MeasureTheory.Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar) (ρ : ℤ → ℂ)
    (hρ : Memℓp ρ 2) (α : Work.BourgainPlan.IonescuWainger.Circle) :
    Work.BourgainPlan.IonescuWainger.opMul Φ (Work.BourgainPlan.IonescuWainger.modSeq ρ α)
        (Work.BourgainPlan.IonescuWainger.memℓp_modSeq hρ α)
      = Work.BourgainPlan.IonescuWainger.modSeq
          (Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstArcTransLp α Φ) ρ hρ) α := by
  apply ftLp_injective
    (opMul_memℓp Φ (modSeq ρ α) (memℓp_modSeq hρ α))
    (memℓp_modSeq (opMul_memℓp (mstArcTransLp α Φ) ρ hρ) α)
  rw [ftLp_opMul Φ (modSeq ρ α) (memℓp_modSeq hρ α),
      ftLp_modSeq (opMul (mstArcTransLp α Φ) ρ hρ) (opMul_memℓp (mstArcTransLp α Φ) ρ hρ) α,
      ftLp_opMul (mstArcTransLp α Φ) ρ hρ]
  simp only [opMulLp]
  rw [ftLp_modSeq ρ hρ α]
  exact opMul_shiftLp Φ α (ftLp ρ hρ)

end Work.BourgainPlan.Maximal
