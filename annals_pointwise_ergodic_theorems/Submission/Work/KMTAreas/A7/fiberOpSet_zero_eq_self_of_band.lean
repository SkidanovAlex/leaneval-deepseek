import Mathlib
import Submission.Work.KMTAreas.A7Hi.windowEnvelopesHasFreqSupport

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "CircB" => Work.BourgainPlan.IonescuWainger.Circle

/-- **The IW symbol of a plateau window is `1` on its band.**  If the periodised window
`Ψ = periodize m` equals `1` on the `δ₁`-arc around `0` and vanishes off the `δ₂`-arc around `0`,
and the frequencies of `A` are `4δ₂`-separated, then `Σ_{α∈A} Ψ(· - α) = 1` on each `δ₁`-arc
`arcSet α₀ δ₁`, `α₀ ∈ A`. -/
theorem iwSymbolSet_eq_one_of_mem_arcSet
    (A : Finset CircB) (m : ℝ → ℂ) (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁₂ : δ₁ ≤ δ₂)
    (hm1 : ∀ θ : CircB, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hm0 : ∀ θ : CircB, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 4 * δ₂ ≤ ‖α - β‖)
    (α₀ : CircB) (hα₀ : α₀ ∈ A) (θ : CircB)
    (hθ : θ ∈ Work.BourgainPlan.IonescuWainger.arcSet α₀ δ₁) :
    Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize m) θ = 1 := by
  have hδ₂ : 0 < δ₂ := lt_of_lt_of_le hδ₁ hδ₁₂
  -- `θ - α₀` lies in the `δ₁`-arc around `0`
  have hsub₁ : θ - α₀ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ := by
    have h := (Work.KMTAreas.A7Hi.arcSet_add_transport (θ - α₀) α₀ α₀ δ₁).mp
      (by rw [sub_add_cancel]; exact hθ)
    simpa using h
  have hone : Work.Analysis.IonescuWainger.periodize m (θ - α₀) = 1 := hm1 _ hsub₁
  -- every other term vanishes
  have hzero : ∀ β ∈ A, β ≠ α₀ →
      Work.Analysis.IonescuWainger.periodize m (θ - β) = 0 := by
    intro β hβ hne
    by_contra hc
    have hsub₂ : θ - β ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂ := hm0 _ hc
    have hsub₁' : θ - α₀ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂ := by
      obtain ⟨t, ht, he⟩ := hsub₁
      exact ⟨t, by linarith [ht, hδ₁₂], he⟩
    have hle : ‖β - α₀‖ ≤ 2 * δ₂ := by
      have hkey : β - α₀ = (θ - α₀) - (θ - β) := by abel
      rw [hkey]
      have h1 : ‖θ - α₀‖ ≤ δ₂ := by
        obtain ⟨t, ht, he⟩ := hsub₁'
        rw [he, zero_add]
        calc ‖((t : ℝ) : CircB)‖ ≤ |t| := Work.KMTAreas.A7Hi.norm_coe_circle_le_abs t
          _ ≤ δ₂ := ht
      have h2 : ‖θ - β‖ ≤ δ₂ := by
        obtain ⟨t, ht, he⟩ := hsub₂
        rw [he, zero_add]
        calc ‖((t : ℝ) : CircB)‖ ≤ |t| := Work.KMTAreas.A7Hi.norm_coe_circle_le_abs t
          _ ≤ δ₂ := ht
      calc ‖(θ - α₀) - (θ - β)‖ ≤ ‖θ - α₀‖ + ‖θ - β‖ := norm_sub_le _ _
        _ ≤ 2 * δ₂ := by linarith
    have hge := hsep α₀ hα₀ β hβ (Ne.symm hne)
    rw [norm_sub_rev] at hge
    linarith
  rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  exact (Finset.sum_eq_single α₀ (fun β hβ hne => hzero β hβ hne)
    (fun h => absurd hα₀ h)).trans hone

/-- **The IW symbol of a plateau window vanishes off its band.**  If the periodised window `Ψ`
vanishes off the `δ₂`-arc around `0`, then `Σ_{α∈A} Ψ(· - α) = 0` at every point off the union of
the `δ₂`-arcs around the points of `A`, stated here in the per-frequency form. -/
theorem iwSymbolSet_eq_zero_of_forall_not_mem_arcSet
    (A : Finset CircB) (m : ℝ → ℂ) (δ₂ : ℝ)
    (hm0 : ∀ θ : CircB, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (θ : CircB) (hθ : ∀ α ∈ A, θ ∉ Work.BourgainPlan.IonescuWainger.arcSet α δ₂) :
    Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize m) θ = 0 := by
  rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  refine Finset.sum_eq_zero fun β hβ => ?_
  by_contra hc
  have hsub : θ - β ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂ := hm0 _ hc
  refine hθ β hβ ?_
  have h := (Work.KMTAreas.A7Hi.arcSet_add_transport (θ - β) β β δ₂).mpr (by simpa using hsub)
  simpa using h


/-- **The `0`-fibre of a plateau window fixes its band.**  If the periodised window
`Ψ = periodize m` equals `1` on the `δ₁`-arc around `0` and vanishes off the `δ₂`-arc around `0`,
the arithmetic frequencies of height exactly `2^l` are `4δ₂`-separated, and `u ∈ ℓ²` is band-limited
to `⋃_{α ∈ A} arcSet α δ₁` (`A = iwArithFreqsNew ρ l`), then the fibre at residue `0`,
`fiberOp ρ l m 0 u`, equals `u`.

Symbolically: `fiberOp ρ l m 0` is the multiplier with symbol `Σ_{α∈A} Ψ(· - α)`, which is `1` on
the band of `u`, so it fixes `u`. -/
theorem fiberOp_zero_eq_self_of_hasFreqSupport
    (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁₂ : δ₁ ≤ δ₂)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (hm1 : ∀ θ : CircB, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₁ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (hm0 : ∀ θ : CircB, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      α ≠ β → 4 * δ₂ ≤ ‖α - β‖)
    (u : ℤ → ℂ) (hu : Memℓp u 2)
    (hband : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        Work.BourgainPlan.IonescuWainger.arcSet α δ₁)) :
    Work.KMTAreas.A7.fiberOp ρ l m 0 u = u := by
  set A := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l with hA
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  have hsym : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize m)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hΨ
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨u, hu⟩ with hF
  set F' : Work.Analysis.IonescuWainger.L2Z :=
    Work.Analysis.IonescuWainger.iwOpSet A (Work.Analysis.IonescuWainger.periodize m) hsym F
    with hF'
  have hfeq : ⇑F' = Work.KMTAreas.A7.fiberOp ρ l m 0 u := by
    rw [fiberOp_zero_eq_iwConv ρ l m hm u,
      Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym F]
  -- the Fourier transforms agree
  have hft : Work.Analysis.IonescuWainger.fourierZ F'
      = Work.BourgainPlan.IonescuWainger.ftLp u hu := by
    have h1 : Work.Analysis.IonescuWainger.fourierZ F'
        = hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize m))
          • Work.Analysis.IonescuWainger.fourierZ F := by
      rw [hF']
      exact Work.Analysis.IonescuWainger.fourierZ_multiplierOf _ hsym F
    rw [h1]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
        (hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize m)))
        (Work.Analysis.IonescuWainger.fourierZ F),
      MeasureTheory.MemLp.coeFn_toLp hsym, hband] with ξ hsmul hσ hb
    rw [hsmul]
    change ⇑(hsym.toLp (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize m))) ξ
        • (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ
      = (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ
    by_cases hmem : ξ ∈ ⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α δ₁
    · simp only [Set.mem_iUnion] at hmem
      obtain ⟨α₀, hα₀, hξα₀⟩ := hmem
      have hσ1 : Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize m) ξ = 1 :=
        iwSymbolSet_eq_one_of_mem_arcSet A m δ₁ δ₂ hδ₁ hδ₁₂ hm1 hm0 hsep α₀ hα₀ ξ hξα₀
      rw [hσ, hσ1, one_smul]
    · have hz : (Work.Analysis.IonescuWainger.fourierZ F : Circ → ℂ) ξ = 0 := hb hmem
      simp only [hz, smul_zero]
  have hFF : F' = F := by
    apply Work.Analysis.IonescuWainger.fourierZ.injective
    rw [hft]
    exact congrArg Work.Analysis.IonescuWainger.fourierZ hF.symm
  have hcoeeq : ⇑F' = ⇑F := congrArg (fun G : Work.Analysis.IonescuWainger.L2Z => ⇑G) hFF
  rw [← hfeq, hcoeeq, hF]

end Work.KMTAreas.A7
