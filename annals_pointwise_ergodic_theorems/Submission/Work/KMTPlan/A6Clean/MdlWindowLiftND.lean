/-
# The window-piece lifts of the §8 packets, with the **correct (input-scale) band**

The §8 adelic form of the frozen slice needs, for every good scale `n`, a family
`W n : Circle → ℝ → ℂ` of band-limited functions whose integer samples are the *window pieces*
`winConvR (mStarF U) (winModR (-α) (mdlSliceF ⋯ n))`.

**Why this file exists.**  Two things are easy to get wrong here, and both were, in the earlier
interface (`windowPieceLiftF`, `mdlSliceF_windowPieceLift`, `vrLiftDataP_packetFamF`):

1. **The band must be the band `γ` of the *input* `h`, not the (larger) support radius of the
   window.**  The transform of the window piece is
   `ξ ↦ periodize m (ξ) · 𝓕h (ξ + α)`; it is supported where `dist (ξ, ℤ) ≤ S` (the window support
   radius, `S = 2^{-2U}` for `m = mStarF U`) **and** `ξ + α` lies in a `γ`-arc around some
   `β ∈ A`.  If `S + γ < ‖α - β‖` for distinct `α, β ∈ A` then only `β = α` can contribute, so the
   window piece is band limited to the `γ`-arc around `0` — *not* to the `S`-arc.  The `γ`-band is
   what the assembly can afford (`Work.KMTPlan.A6.goodScale_two_pow_bands_le`:
   `2^{k₁-logN} + 2^{d(k₂-logN)} ≤ 1/(8Q)`), because it is an inequality *about the data*, whereas
   the fixed bound `1/(16Q)` of the earlier interface is **false**: `goodScale Q L N` only gives
   `N ≥ 8Q2^{L+1}`, hence `δ n = 2^{k₁-logN ⌊a n⌋} ≤ 1/(8Q)`, and this is attained (take `Q` a power
   of two, `N = 8Q2^{L+1}`, `k₁ = L`).  A band-limited function is determined by its integer
   samples, so for such data *no* band-`1/(16Q)` lift of the window piece exists.

2. **The window's flatness is irrelevant.**  Only the *support* of the periodised window enters: the
   earlier `Work.KMTAreas.A7Hi.windowEnvelopesHasFreqSupport` assumes flatness on the band but never
   uses it in its proof.  With the parameters separated (window support `S`, input band `γ`) the
   flatness hypothesis disappears.

## Contents

* `mStargF_eq_mStarF` — the `g`-side window is the `f`-side window at scale `d·U`;
* `windowPieceBand_abs` — the **band of the window piece** at the input's scale (the key new fact);
* `windowPieceLift_abs` — the **abstract lift**;
* `sep_le_of_uScale` — the separation of `(ℚ/ℤ)_{≤ l}` at the model scale.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam
import Submission.Work.KMTPlan.A6Clean.liftOfArcSamples
import Submission.Work.KMTPlan.A6Clean.L2BandSupport
import Submission.Work.KMTPlan.A6Clean.bandRadius_le
import Submission.Work.KMTPlan.A6.MdlAdelicPackets

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The `g`-side window `m̃_* = η_{≤-2du}` is the `f`-side window at scale `d·u`. -/
lemma mStargF_eq_mStarF (d u : ℕ) :
    Work.KMTAreas.A7.mStargF d u = Work.KMTAreas.A7.mStarF (d * u) := by
  simp only [Work.KMTAreas.A7.mStargF, Work.KMTAreas.A7.mStarF]
  congr 1
  push_cast
  ring

/-- **The band of the window piece, at the scale of the *input*.**  Let `m` be a window whose
periodisation is supported in the `S`-arc around `0`, let `A` be a finite set of frequencies whose
elements are `(S + γ)`-separated, and let `h ∈ ℓ²(ℤ)` be band limited to the `γ`-arcs around `A`.
Then for every `α ∈ A` the window piece `winConvR m (winModR (-α) h)` is band limited to the
`γ`-arc around `0`. -/
theorem windowPieceBand_abs {m : ℝ → ℂ} (hm : Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    {S : ℝ} (hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 S)
    {A : Finset Circ} {γ : ℝ}
    (h : ℤ → ℂ) (hh : Memℓp h 2)
    (hhE : Work.BourgainPlan.IonescuWainger.HasFreqSupport h hh
      (⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α γ))
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → S + γ < ‖α - β‖)
    (α : Circ) (hα : α ∈ A) :
    ∃ hw : Memℓp (Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h)) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h)) hw
        (Work.BourgainPlan.IonescuWainger.arcSet 0 γ) := by
  classical
  have hΨ : MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  obtain ⟨hv, hsuppv⟩ := Work.KMTAreas.A7Hi.hasFreqSupport_winModRep_sub hh hhE α
  obtain ⟨hw, hftw⟩ := Work.KMTAreas.A7Hi.winConvRep_ftLp_ae m hm hΨ hv
  obtain ⟨hγ, hbγ⟩ : ∃ hw' : Memℓp
      (Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) h)) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) h)) hw'
        (Work.BourgainPlan.IonescuWainger.arcSet 0 γ) := by
    refine ⟨hw, ?_⟩
    simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hsuppv ⊢
    filter_upwards [hftw, hsuppv] with ξ hftwξ hsuppvξ hmem
    rw [hftwξ]
    by_cases hper : Work.Analysis.IonescuWainger.periodize m ξ = 0
    · rw [hper, zero_mul]
    · have hS : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 S := hmsup ξ hper
      have hv0 : (Work.BourgainPlan.IonescuWainger.ftLp
          (Work.KMTAreas.A7Rep.winModRep (-α) h) hv : Circ → ℂ) ξ = 0 := by
        by_contra h2
        have hmem2 : ξ ∈ ⋃ β ∈ A,
            Work.BourgainPlan.IonescuWainger.arcSet (β - α) γ := by
          by_contra hcon
          exact h2 (hsuppvξ hcon)
        obtain ⟨β, hβmem, hβarc⟩ := Set.mem_iUnion₂.mp hmem2
        have hn1 : ‖ξ‖ ≤ S := by
          obtain ⟨θ, hθ, hθeq⟩ := hS
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
        have hβα : ‖β - α‖ ≤ S + γ := by
          have h3 : ‖β - α‖ ≤ ‖ξ‖ + ‖ξ - (β - α)‖ := by
            have heq : β - α = ξ - (ξ - (β - α)) := by abel
            calc ‖β - α‖ = ‖ξ - (ξ - (β - α))‖ := congrArg Norm.norm heq
              _ ≤ ‖ξ‖ + ‖ξ - (β - α)‖ := norm_sub_le ξ (ξ - (β - α))
          linarith
        have hne : β ≠ α := fun hab => hmem (by simpa [hab] using hβarc)
        have hle : ‖α - β‖ ≤ S + γ := by rw [norm_sub_rev]; exact hβα
        exact absurd (hsep α hα β hβmem (Ne.symm hne)) (not_lt.mpr hle)
      rw [hv0, mul_zero]
  exact ⟨hγ, hbγ⟩

/-- **The abstract window-piece lift.**  Let `h ∈ ℓ²(ℤ)` be band limited to the `γ`-arcs around a
finite set `A` of frequencies, let `m` be a window whose periodisation is supported in the `S`-arc
around `0`, and suppose `S + γ < ‖α - β‖` for distinct `α, β ∈ A` and `γ < 1/2`.  Then there is a
family `W : Circle → ℝ → ℂ` of band-`γ` functions whose integer samples are the window pieces
`winConvR m (winModR (-α) h)`, vanishing off `A`. -/
theorem windowPieceLift_abs {m : ℝ → ℂ} (hm : Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    {S : ℝ} (hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 S)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (A : Finset Circ) (h : ℤ → ℂ) (hh : Memℓp h 2)
    (hhE : Work.BourgainPlan.IonescuWainger.HasFreqSupport h hh
      (⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α γ))
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → S + γ < ‖α - β‖) :
    ∃ W : Circ → ℝ → ℂ,
      (∀ α, Measurable (W α)) ∧
      (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-γ) γ)) ∧
      (∀ α, α ∉ A → W α = 0) ∧
      (∀ α ∈ A, ∀ x : ℤ, W α (x : ℝ) =
        Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h) x) := by
  classical
  have hpiece : ∀ α ∈ A, ∃ hw : Memℓp
        (Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h)) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) h)) hw
        (Work.BourgainPlan.IonescuWainger.arcSet 0 γ) :=
    fun α hα => windowPieceBand_abs (A := A) (γ := γ) hm hmsum hmsup h hh hhE hsep α hα
  have hex : ∀ α : Circ, ∃ F : ℝ → ℂ, MemLp F 2 volume ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-γ) γ → F ξ = 0) ∧
      (∀ x : ℤ, (if α ∈ A then Work.KMTAreas.A7.winConvR m
            (Work.KMTAreas.A7.winModR (-α) h) x else 0)
        = FourierTransformInv.fourierInv F (x : ℝ)) := by
    intro α
    by_cases hα : α ∈ A
    · obtain ⟨hw, hsup⟩ := hpiece α hα
      obtain ⟨F, hFmem, hFsupp, hFeq⟩ := liftOfArcSamples hγ0 hγ1 _ hw hsup
      exact ⟨F, hFmem, hFsupp, fun x => by rw [if_pos hα]; exact hFeq x⟩
    · refine ⟨0, MeasureTheory.MemLp.zero, by simp, fun x => ?_⟩
      rw [if_neg hα, Work.KMTAreas.fourierInv_zero_fun]
      rfl
  choose Wamp hWmem hWsupp hWeq using hex
  refine ⟨fun α X => if α ∈ A then FourierTransformInv.fourierInv (Wamp α) X else 0,
    ?_, ?_, ?_, ?_⟩
  · intro α
    by_cases hα : α ∈ A
    · simp only [hα, if_true]
      exact (Work.KMTPlan.A6.continuous_of_hasRealFreqSupport
        (hasRealFreqSupport_of_hasL2FreqSupport measurableSet_Icc (by simp)
          ⟨Wamp α, hWmem α, hWsupp α, fun t => rfl⟩)).measurable
    · simp only [hα, if_false]
      exact measurable_const
  · intro α
    by_cases hα : α ∈ A
    · simp only [hα, if_true]
      exact hasRealFreqSupport_of_hasL2FreqSupport measurableSet_Icc (by simp)
        ⟨Wamp α, hWmem α, hWsupp α, fun t => rfl⟩
    · simp only [hα, if_false]
      exact hasRealFreqSupport_zero _
  · intro α hα
    simp only [hα, if_false]
    funext X
    rfl
  · intro α hα x
    simp only [hα, if_true]
    have h := hWeq α x
    rw [if_pos hα] at h
    exact h.symm

/-- **The separation of the arithmetic frequencies of height `≤ l` at the model scale.**  With `C`
the constant of `Work.Analysis.IonescuWainger.iw_height_separated`, if
`C·2^{ρl} + 2 ≤ 2·uScale ρ L` (with `l ≤ L`) then distinct elements of `(ℚ/ℤ)_{≤l}` are at
distance at least `4·2^{-2·uScale ρ L}`. -/
theorem sep_le_of_uScale {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l L : ℕ), l ≤ L →
      C * (2 : ℝ) ^ (ρ * (l : ℝ)) + 2 ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) →
      ∀ ⦃α β : Circ⦄,
        α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l →
        β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l → α ≠ β →
        4 * (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ L : ℝ))) ≤ ‖α - β‖ := by
  obtain ⟨C, hC, hsep⟩ := Work.Analysis.IonescuWainger.iw_height_separated hρ
  refine ⟨C, hC, ?_⟩
  intro l L hl hth α β hα hβ hne
  have h1 := hsep l hα hβ hne
  have hlR : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
  have hexp2 : ρ * (l : ℝ) ≤ ρ * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hlR hρ.le
  have hmono : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp2
  have hkey : C * (2 : ℝ) ^ (ρ * (l : ℝ)) + 2
      ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) :=
    le_trans (by linarith [hmono]) hth
  have hz : (4 : ℝ) * (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)))
      ≤ (2 : ℝ) ^ (-(C * (2 : ℝ) ^ (ρ * (l : ℝ)))) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [h4, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have harg : (2 : ℝ) + -(2 * (Work.KMTAreas.A7.uScale ρ L : ℝ))
        ≤ -(C * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
      linarith [hkey]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) harg
  linarith [h1]

end Work.KMTPlan.A6Clean
