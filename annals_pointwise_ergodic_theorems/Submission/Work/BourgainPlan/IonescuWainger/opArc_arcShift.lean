import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_mul_pow

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

noncomputable section

/-- The Fourier transform of a modulation `modSeq ρ θ` is the translate by `θ` of the Fourier
transform of `ρ`: both are the `L²(𝕋)` class whose `i`-th Fourier coefficient is
`ρ i · e^{2πi i θ}`. -/
theorem ftLp_modSeq (ρ : ℤ → ℂ) (hρ : Memℓp ρ 2) (θ : Circle) :
    ftLp (modSeq ρ θ) (memℓp_modSeq hρ θ) = shiftLp θ (ftLp ρ hρ) := by
  refine (fourierBasis (T := 1)).repr.injective ?_
  ext i
  rw [repr_ftLp (memℓp_modSeq hρ θ) i, repr_shiftLp hρ θ i]
  unfold modSeq
  rw [mul_comm]

/-- The symbol of the translated arc set `E + α` is the translate by `α` of the symbol of `E`. -/
theorem arcSymbol_arcShift_apply' (φ : Circle → ℂ) (E : Finset Circle) (α ξ : Circle) :
    arcSymbol φ (arcShift E α) ξ = arcSymbol φ E (ξ + (-α)) := by
  rw [arcSymbol_arcShift, arcSymbol_apply]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  congr 1
  abel

/-- The modulation identity for the arc symbols at the level of `L²(𝕋)`: translating the arc set
`E` by `α` conjugates the multiplier with symbol `arcSymbol φ E` by the translation operator
`shiftLp (-α)`, and at the same time the input is modulated by `shiftLp α`. -/
theorem arcShift_modulation_lp (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (E : Finset Circle) (α : Circle)
    (F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    (arcSymbolLp φ hφ (arcShift E α)) • F
      = shiftLp (-α) ((arcSymbolLp φ hφ E) • (shiftLp α F)) := by
  refine Lp.ext ?_
  have hmp : MeasurePreserving (fun x : Circle => x + (-α))
      (AddCircle.haarAddCircle (T := 1)) (AddCircle.haarAddCircle (T := 1)) :=
    measurePreserving_add_right _ (-α)
  set A : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    arcSymbolLp φ hφ (arcShift E α) with hAdef
  set B : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) := arcSymbolLp φ hφ E with hBdef
  set X : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := B • (shiftLp α F) with hXdef
  have e1 : ((A • F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => (A : Circle → ℂ) ξ * (F : Circle → ℂ) ξ :=
    Lp.coeFn_lpSMul A F
  have e2 : ((A : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ (arcShift E α) := by
    rw [hAdef]; exact arcSymbolLp_coeFn φ hφ (arcShift E α)
  have e3 : ((shiftLp (-α) X : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ => (X : Circle → ℂ) (ξ + (-α)) :=
    shiftLp_coeFn (-α) X
  have e4 : ((X : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      fun ξ => (B : Circle → ℂ) ξ * (shiftLp α F : Circle → ℂ) ξ := by
    rw [hXdef]; exact Lp.coeFn_lpSMul B (shiftLp α F)
  have e5 : ((shiftLp α F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ => (F : Circle → ℂ) (ξ + α) :=
    shiftLp_coeFn α F
  have e6 : ((B : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ E := by
    rw [hBdef]; exact arcSymbolLp_coeFn φ hφ E
  filter_upwards [e1, e2, e3, hmp.quasiMeasurePreserving.ae e4,
    hmp.quasiMeasurePreserving.ae e5, hmp.quasiMeasurePreserving.ae e6]
    with ξ h1 h2 h3 h4 h5 h6
  rw [h1, h3, h4, h5, h6, h2, arcSymbol_arcShift_apply']
  rw [show (ξ + (-α)) + α = ξ from by abel]

/-- `ftLp` is injective: an `ℓ²(ℤ)`-sequence is determined by its Fourier transform. -/
theorem ftLp_injective {a b : ℤ → ℂ} (ha : Memℓp a 2) (hb : Memℓp b 2)
    (h : ftLp a ha = ftLp b hb) : a = b := by
  have h1 : fourierBasis.repr (ftLp a ha) = (⟨a, ha⟩ : lp (fun _ : ℤ => ℂ) 2) := by
    simp only [ftLp]; exact LinearIsometryEquiv.symm_apply_apply _ _
  have h2 : fourierBasis.repr (ftLp b hb) = (⟨b, hb⟩ : lp (fun _ : ℤ => ℂ) 2) := by
    simp only [ftLp]; exact LinearIsometryEquiv.symm_apply_apply _ _
  have hh := congrArg (fun x => fourierBasis.repr x) h
  rw [h1, h2] at hh
  exact congrArg (fun x : lp (fun _ : ℤ => ℂ) 2 => (x : ℤ → ℂ)) hh

/-- **The modulation identity for the arc multipliers `Op_{φ;E}`** (Tao, arXiv:2008.05066, proof of the real-form multiplier result: "which by the modulation symmetries of the Fourier transform imply that ..."): translating the arc set `E` by `α` is the same as conjugating the multiplier with symbol `Σ_{β ∈ E} φ(· - β)` by the modulation `ρ ↦ (n ↦ ρ n · e(n α))`.

Concretely, the symbol of `opArc φ hφ (arcShift E α)` is `ξ ↦ Σ_{β ∈ E} φ(ξ - (β + α)) = Φ(ξ - α)` with `Φ = arcSymbol φ E`, and `modSeq ρ θ` has Fourier transform `η ↦ 𝓕ρ (η + θ)` (`hasFreqSupport_modSeq` / its helper `repr_shift`), so the identity follows from `𝓕 opArc = Φ · 𝓕` (`ftLp_opMul`) plus the elementary `Φ(ξ - α) 𝓕f (ξ) = Φ(ξ - α) 𝓕(modSeq f α)(ξ - α)`. -/
theorem opArc_arcShift (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle)
    (α : Work.BourgainPlan.IonescuWainger.Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ
        (Work.BourgainPlan.IonescuWainger.arcShift E α) f hf
      = Work.BourgainPlan.IonescuWainger.modSeq
          (Work.BourgainPlan.IonescuWainger.opArc φ hφ E
            (Work.BourgainPlan.IonescuWainger.modSeq f α)
            (Work.BourgainPlan.IonescuWainger.memℓp_modSeq hf α)) (-α) := by
  apply ftLp_injective
    (opMul_memℓp (arcSymbolLp φ hφ (arcShift E α)) f hf)
    (memℓp_modSeq (opMul_memℓp (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α)) (-α))
  have h1 : ftLp (opMul (arcSymbolLp φ hφ (arcShift E α)) f hf)
      (opMul_memℓp (arcSymbolLp φ hφ (arcShift E α)) f hf)
      = arcSymbolLp φ hφ (arcShift E α) • ftLp f hf := ftLp_opMul _ f hf
  have h2 : ftLp (modSeq (opMul (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α)) (-α))
      (memℓp_modSeq (opMul_memℓp (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α)) (-α))
      = shiftLp (-α) (ftLp (opMul (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α))
          (opMul_memℓp (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α))) :=
    ftLp_modSeq (opMul (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α))
      (opMul_memℓp (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α)) (-α)
  have h3 : ftLp (opMul (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α))
      (opMul_memℓp (arcSymbolLp φ hφ E) (modSeq f α) (memℓp_modSeq hf α))
      = arcSymbolLp φ hφ E • ftLp (modSeq f α) (memℓp_modSeq hf α) := ftLp_opMul _ _ _
  have h4 : ftLp (modSeq f α) (memℓp_modSeq hf α) = shiftLp α (ftLp f hf) :=
    ftLp_modSeq f hf α
  rw [h1, h2, h3, h4]
  exact arcShift_modulation_lp φ hφ E α (ftLp f hf)

end

end Work.BourgainPlan.IonescuWainger
