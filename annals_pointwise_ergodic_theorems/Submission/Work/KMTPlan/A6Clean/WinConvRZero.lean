/-
# The window pieces vanish off the exact height

For the §8 packets of the model slice one has to replace the fibre decomposition's sum over the
height-`≤ l` arithmetic frequencies by the sum over the **exact-height** frequencies
`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`: only then is the packet minor arc (which is what
carries the arithmetic gain `2^{-c·l}`).  The algebraic step is the present lemma: the window piece
`winConvR m (winModR (-α) h)` — the `α`-th window envelope of the input `h` — **vanishes** for
every `α` of height `≤ l` which is not of exact height `l`, provided

* the window `m` is supported in `[-2δ, 2δ]`,
* `h` is band-limited to the `γ`-arcs around the exact-height frequencies (`h` is the model input
  `Tle ρ l φ (mdlF ⋯)`, whose band is exact-height by `Tle_exact_band`), and
* `2δ + γ` is below the separation of the arithmetic frequencies.

The proof is the Fourier side: the transform of the window piece is
`periodize m (ξ) · 𝓕(winModR (-α) h)(ξ)`, with the first factor supported in the `2δ`-arc around `0`
and the second in the `γ`-arcs around `β - α`, `β ∈ diffFreqs ρ l`.  A common point would force
`‖β - α‖ ≤ 2δ + γ`, contradicting the separation (`α ∉ diffFreqs ρ l` excludes `β = α`); hence the
transform vanishes a.e., and the sequence vanishes by injectivity of the Fourier transform
(`fourierCoeff_ftLp`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelLargeHiRep
import Submission.Work.KMTAreas.A7Hi.FiberOpCutFixGeneral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

theorem winConvR_eq_zero_of_not_exact (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (m : ℝ → ℂ) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (hmsupp : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0)
    (h : ℤ → ℂ) (hh : Memℓp h 2)
    (hhE : Work.BourgainPlan.IonescuWainger.HasFreqSupport h hh
      (⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l, Work.BourgainPlan.IonescuWainger.arcSet β γ))
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l, α ≠ β → 2 * δ + γ < ‖α - β‖)
    (α : Work.Analysis.IonescuWainger.Circle)
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (hα' : α ∉ Work.KMTAreas.A7.diffFreqs ρ l) :
    Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h) = 0 := by
  classical
  -- the modulation is `ℓ²` with the shifted band
  obtain ⟨hv, hbandv⟩ := Work.KMTAreas.A7Hi.hasFreqSupport_winModRep_sub hh hhE α
  -- the periodised window is `L^∞`
  have hΨ : MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  -- the window piece is `ℓ²` with transform the product of the two symbols
  obtain ⟨hw, hftw⟩ := Work.KMTAreas.A7Hi.winConvRep_ftLp_ae m hm hΨ hv
  -- the product vanishes a.e.
  have hprod : ((fun ξ : Circ => Work.Analysis.IonescuWainger.periodize m ξ *
      (Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7Rep.winModRep (-α) h) hv :
        Circ → ℂ) ξ) : Circ → ℂ) =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] 0 := by
    filter_upwards [hbandv] with ξ hbandvξ
    by_cases h1 : Work.Analysis.IonescuWainger.periodize m ξ = 0
    · simp [h1]
    · have hsupp' : ∀ y : ℝ, m y ≠ 0 → |y| ≤ 2 * δ := by
        intro y hy
        by_contra hcon
        exact hy (hmsupp y (lt_of_not_ge hcon))
      have hmem1 : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ) :=
        Work.KMTAreas.A7Hi.periodize_support_mem_arcSet hsupp' h1
      have h2 : (Work.BourgainPlan.IonescuWainger.ftLp
          (Work.KMTAreas.A7Rep.winModRep (-α) h) hv : Circ → ℂ) ξ = 0 := by
        by_contra h2ne
        have hmem2 : ξ ∈ ⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l,
            Work.BourgainPlan.IonescuWainger.arcSet (β - α) γ := by
          by_contra hcon
          exact h2ne (hbandvξ hcon)
        obtain ⟨β, hβmem, hβarc⟩ := Set.mem_iUnion₂.mp hmem2
        -- the two norms
        have hn1 : ‖ξ‖ ≤ 2 * δ := by
          obtain ⟨θ, hθ, hθeq⟩ := hmem1
          rw [zero_add] at hθeq
          rw [hθeq]
          exact le_trans (Work.KMTAreas.A7Hi.norm_coe_circle_le_abs θ) hθ
        have hsub : ξ - (β - α) ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 γ := by
          have h := (Work.KMTAreas.A7Hi.arcSet_add_transport (ξ - (β - α)) (β - α)
            (β - α) γ).mp (by simpa using hβarc)
          simpa [sub_self] using h
        have hn2 : ‖ξ - (β - α)‖ ≤ γ := by
          obtain ⟨θ, hθ, hθeq⟩ := hsub
          rw [zero_add] at hθeq
          rw [hθeq]
          exact le_trans (Work.KMTAreas.A7Hi.norm_coe_circle_le_abs θ) hθ
        have hβα : ‖β - α‖ ≤ 2 * δ + γ := by
          have h3 : ‖β - α‖ ≤ ‖ξ‖ + ‖ξ - (β - α)‖ := by
            have heq : β - α = ξ - (ξ - (β - α)) := by abel
            calc ‖β - α‖ = ‖ξ - (ξ - (β - α))‖ := congrArg Norm.norm heq
              _ ≤ ‖ξ‖ + ‖ξ - (β - α)‖ := norm_sub_le ξ (ξ - (β - α))
          linarith
        have hne : α ≠ β := fun hab => hα' (by rw [hab]; exact hβmem)
        have hrev : ‖α - β‖ = ‖β - α‖ := norm_sub_rev α β
        linarith [hsep α hα β hβmem hne, hβα, hrev]
      simp [h2]
  -- the transform of the window piece vanishes a.e., hence the window piece vanishes
  have hft0 : ((Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7Rep.winConvRep m
      (Work.KMTAreas.A7Rep.winModRep (-α) h)) hw : Circ → ℂ))
      =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] 0 := hftw.trans hprod
  have hzero : Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) h) = 0 := by
    funext n
    have h1 := Work.KMTAreas.A7Rep.fourierCoeff_ftLp hw n
    have h2 : fourierCoeff ((Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7Rep.winConvRep m
        (Work.KMTAreas.A7Rep.winModRep (-α) h)) hw : Circ → ℂ)) n
        = fourierCoeff (0 : Circ → ℂ) n :=
      congrFun (fourierCoeff_congr_ae hft0) n
    have h3 : fourierCoeff (0 : Circ → ℂ) n = 0 := by
      simp only [fourierCoeff, Pi.zero_apply, smul_zero, integral_zero]
    rw [h1, h3] at h2
    simpa using h2
  have hbridge : Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) h)
      = Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h) := rfl
  rw [hbridge] at hzero
  exact hzero

end Work.KMTPlan.A6Clean
