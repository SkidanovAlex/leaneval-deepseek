/-
# The band-limited fibre variational sampling estimate

`Work.KMTAreas.A7.fibreVarSampling_of_bandLimited`: for a family `w` of sequences whose `n`-th
member is \(\ell^2\) and band-limited to the union of the narrow arcs
`arcSet α (W n)`, `α ∈ iwArithFreqsNew ρ l₁` (the exact-height arithmetic frequencies), with
`W n ≤ 2^{-2U-1}`, `W n · q ≤ 1/8`, the frequencies `q`-torsion and `4·2^{-2U}`-separated,

  `‖ residueLp p q (n₀ ↦ V^r_n (fiberOp ρ l₁ (mStarF U) n₀ (w n))) ‖_{ℓᵖ}`
      `≤ C ‖ V^r_n (w n) ‖_{ℓᵖ}`,

with `C` depending only on `p` and `r`.

## The proof

The two synthesis identities of `A7Hi/FiberVarSampling.lean`
(`winSynth_windowEnvelopes`, `winRot_windowEnvelopes`) together with the periodicity
`fiberOp_add_q` of the fibre in the residue identify the target with the **packet-rotation bound**
for the *window envelopes* `g n α = windowEnvelopes (mStarF U) (w n) α`
(`Work.KMTAreas.A7Hi.fiberVarSampling_of_windowCrux`), whose right-hand side is
`‖V^r_n (fiberOp ρ l₁ (mStarF U) 0 (w n))‖_{ℓᵖ}`.

Two inputs supply the rest.

* The **range identity** `fiberOp ρ l₁ (mStarF U) 0 (w n) = w n`: on the band, the `mStarF U`-cut
  is the identity.  This is `fiberOp_zero_eq_self_of_hasFreqSupport` (imported from
  `A7/fiberOpSet_zero_eq_self_of_band.lean`), applied with `δ₁ = W n` and `δ₂ = 2^{-2U}`.
  (The *unrestricted* range identity is false — `NOTES_A7Hi_FiberVarSampling_SESSION8.md` §2 — so
  the band hypothesis is what makes this step available.)
* The **band limitation of the envelopes**: each `g n α` is band-limited to a *single* narrow arc
  `arcSet 0 δ` with `δ q ≤ 1/8`.  Here `δ = 1/(8q) ≥ W n`: the envelope is the `mStarF U`-cut of
  the `(-α)`-modulation of `w n`, whose spectrum is the intersection of `arcSet 0 (2^{-2U})` with
  the union of the `W n`-arcs at `β - α`; the separation of the frequencies kills every `β ≠ α`,
  leaving `arcSet 0 (W n)`.  This is
  `windowEnvelopesHasFreqSupport_twoRadius` below, a two-radius version of
  `A7Hi.windowEnvelopesHasFreqSupport` (whose single radius cannot be used: the periodisation of
  `mStarF U` is supported in the `2^{-2U}`-arc, which is *larger* than the `2 W n`-arc).
  The band limitation is then consumed by
  `Work.KMTAreas.A7Hi.PacketRotationResidueBoundLpGeTwo` (proved).

The elementary supporting lemmas (`notMem_iUnion_arcSet_sub_of_separated_gen`,
`summable_cw_mul_of_memℓp`, `periodize_mStarF_mem_arcSet`) are proved in this file.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarSampling
import Submission.Work.KMTAreas.A7.arithSymb_eq_of_spike

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators ENNReal

-- `hU` and `hq` appear only in the hypotheses of the target, not in its conclusion.
set_option linter.unusedVariables false

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section


/-! ## The two-radius separation geometry -/

/-- The separation geometry of the arcs, with independent radii. -/
lemma notMem_iUnion_arcSet_sub_of_separated_gen
    (A : Finset Circ) (δ₂ δ_out δ_in : ℝ)
    (hδin : δ_in ≤ δ_out)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → δ₂ + δ_in < ‖α - β‖)
    (α : Circ) (hα : α ∈ A) (ξ : Circ)
    (hξout : ξ ∉ Work.BourgainPlan.IonescuWainger.arcSet 0 δ_out)
    (hξ₂ : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂) :
    ξ ∉ ⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet (β - α) δ_in := by
  intro hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨β, hβ, hmemβ⟩ := hmem
  rcases eq_or_ne β α with rfl | hne
  · refine hξout (arcSet_mono hδin 0 ?_)
    simpa using hmemβ
  · rcases hmemβ with ⟨θ₁, hθ₁, hξ₁⟩
    rcases hξ₂ with ⟨θ₂, hθ₂, hξ₂⟩
    have hβα : β - α = ((θ₂ - θ₁ : ℝ) : Circ) := by
      have h1 : β - α + (θ₁ : Circ) = (θ₂ : Circ) := by rw [← hξ₁, hξ₂, zero_add]
      have h2' : β - α = (θ₂ : Circ) - (θ₁ : Circ) := eq_sub_iff_add_eq.mpr h1
      rw [h2']; norm_cast
    have hnorm : ‖β - α‖ ≤ δ₂ + δ_in := by
      rw [hβα]
      have h3 : ‖((θ₂ - θ₁ : ℝ) : Circ)‖ ≤ |θ₂ - θ₁| :=
        Work.KMTAreas.A7Hi.norm_coe_circle_le_abs (θ₂ - θ₁)
      have h4 : |θ₂ - θ₁| ≤ |θ₂| + |θ₁| := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [le_abs_self θ₂, neg_abs_le θ₂, le_abs_self θ₁, neg_abs_le θ₁]
      have h5 : |θ₂| ≤ δ₂ := by
        have := abs_nonneg θ₂; linarith
      linarith
    have h7 : δ₂ + δ_in < ‖α - β‖ := hsep α hα β hβ (Ne.symm hne)
    rw [norm_sub_rev α β] at h7
    linarith

/-! ## The window envelope of a band-limited input, two radii -/

/-- **The window envelope of a band-limited input is band-limited to a (possibly smaller) arc.**
If the periodisation of the window `m` is supported in the `δ₂`-arc around `0`, the windows of `A`
are separated by more than `δ₂ + δ_in`, and `u ∈ ℓ²(ℤ)` is band-limited to the union of the
`δ_in`-arcs around the points of `A`, then for `α ∈ A` the envelope
`T_m (M_{-α} u) = 𝓕⁻(periodize m · 𝓕M_{-α}u)` is square-summable and band-limited to the
`δ_out`-arc around `0`. -/
lemma windowEnvelopesHasFreqSupport_twoRadius
    (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖cw m j‖))
    (δ₂ δ_out δ_in : ℝ) (hδin : δ_in ≤ δ_out)
    (hmsup : ∀ θ : Circ,
      Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂)
    (A : Finset Circ)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → δ₂ + δ_in < ‖α - β‖)
    (u : ℤ → ℂ) (hu : Memℓp u 2)
    (huE : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α δ_in))
    (α : Circ) (hα : α ∈ A) :
    ∃ hh : Memℓp (Work.KMTAreas.A7Rep.winConvRep m
        (Work.KMTAreas.A7Rep.winModRep (-α) u)) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) u)) hh
        (Work.BourgainPlan.IonescuWainger.arcSet 0 δ_out) := by
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7Hi.periodizeMemLpTop hm hmsum
  obtain ⟨hv, hsuppv⟩ := Work.KMTAreas.A7Hi.hasFreqSupport_winModRep_sub hu huE α
  obtain ⟨hw, hftw⟩ := Work.KMTAreas.A7Hi.winConvRep_ftLp_ae m hm hΨ hv
  refine ⟨hw, ?_⟩
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hsuppv ⊢
  filter_upwards [hftw, hsuppv] with ξ hftwξ hsuppvξ hmem
  rw [hftwξ]
  by_cases hper : Work.Analysis.IonescuWainger.periodize m ξ = 0
  · rw [hper, zero_mul]
  · have h2 : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ₂ := hmsup ξ hper
    have hsepξ : ξ ∉ ⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet (β - α) δ_in :=
      notMem_iUnion_arcSet_sub_of_separated_gen A δ₂ δ_out δ_in hδin hsep α hα ξ hmem h2
    rw [hsuppvξ hsepξ, mul_zero]

/-! ## The convolution of an `ℓ¹` symbol with an `ℓ²` sequence -/

/-- The convolution `j ↦ cw m j · u (x - j)` of the Fourier coefficients of an integrable window
with a square-summable sequence is absolutely summable. -/
lemma summable_cw_mul_of_memℓp {m : ℝ → ℂ} (hmsum : Summable (fun j : ℤ => ‖cw m j‖))
    {u : ℤ → ℂ} (hu : Memℓp u 2) (x : ℤ) :
    Summable (fun j : ℤ => cw m j * u (x - j)) := by
  have h1 : Summable (fun j : ℤ => ‖cw m j‖ * ‖cw m j‖) := by
    have h0 : Summable (fun x : ℤ × ℤ => ‖cw m x.1‖ * ‖cw m x.2‖) :=
      hmsum.mul_of_nonneg hmsum (fun j => norm_nonneg _) (fun j => norm_nonneg _)
    refine h0.comp_injective (i := fun j : ℤ => (j, j)) (fun a b hab => ?_)
    simpa using hab
  have huu : Summable (fun j : ℤ => ‖u j‖ ^ (2 : ℝ)) := by simpa [Memℓp] using hu
  have h2 : Summable (fun j : ℤ => ‖u (x - j)‖ * ‖u (x - j)‖) := by
    have h3 : Summable (fun j : ℤ => ‖u (x - j)‖ ^ (2 : ℝ)) :=
      huu.comp_injective (i := fun j : ℤ => x - j) (fun a b hab => by
      have h1 : a - x = b - x := by
        have h2 := congrArg Neg.neg hab
        rwa [neg_sub, neg_sub] at h2
      exact add_right_cancel h1)
    refine h3.congr fun j => ?_
    rw [Real.rpow_two, pow_two]
  refine Summable.of_norm_bounded (h1.add h2) fun j => ?_
  rw [norm_mul]
  nlinarith [norm_nonneg (cw m j), norm_nonneg (u (x - j)), sq_nonneg (‖cw m j‖ - ‖u (x - j)‖)]

/-! ## The periodisation of `mStarF` -/

/-- A nonvanishing value of the periodisation of `mStarF U` forces its argument into the
`2^{-2U}`-arc around the origin. -/
lemma periodize_mStarF_mem_arcSet {U : ℕ} {θ : Circ}
    (h : Work.Analysis.IonescuWainger.periodize (mStarF U) θ ≠ 0) :
    θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ((2 : ℝ) ^ (-(2 * (U : ℤ)))) := by
  obtain ⟨θ₀, hθ₀eq, hθ₀le⟩ :=
    arithSymbSpike_exists_coe_abs_le_of_periodize_ne_zero (arithSymbSpike_mStarF_support U) h
  exact ⟨θ₀, hθ₀le, by rw [← hθ₀eq, zero_add]⟩


/-! ## The target -/

end

end Work.KMTAreas.A7
