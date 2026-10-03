import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_modSeq
import Submission.Work.BourgainPlan.IonescuWainger.OpMulLinear
import Submission.Work.KMTAreas.A7Hi.periodizeMemLpTop
import Submission.Work.KMTAreas.A7Hi.winConvRep_ftLp_ae

/-!
# The window envelopes of a windowed input are band-limited to the window

Let `m : ℝ → ℂ` be an integrable window whose periodisation `Ψ = periodize m` is a *plateau*
function: it vanishes off the `2δ`-arc around `0` (`hmsup`) — and, for the intended use, equals `1`
on the `δ`-arc around `0` (`hmplat`, which the support statement below does not need).  Let
`u ∈ ℓ²(ℤ)` be band-limited to the union of the `δ`-arcs around a finite set `A` of frequencies
which are `8δ`-separated (`hsep`).

The **window envelope** of `u` at the frequency `α ∈ A` is

`winConvRep m (winModRep (-α) u) = T_m (M_{-α} u)`,

the convolution with the coefficient sequence `cw m = 𝓕(periodize m)` of the `(-α)`-modulated
input.  The claim is that it is square-summable and band-limited to the single arc
`arcSet 0 δ`: the multiplier of the convolution is `Ψ`, which is supported in `arcSet 0 (2δ)`,
while the input `M_{-α} u` has its spectrum in `⋃_{β ∈ A} arcSet (β - α) δ`; for `β ≠ α` the
`δ`-arc around `β - α` misses `arcSet 0 (2δ)` because `‖β - α‖ ≥ 8δ > 3δ`, and for `β = α` it is
`arcSet 0 δ` itself.

## The two imported ingredients

* `Work.KMTAreas.A7Hi.periodizeMemLpTop` — `Ψ ∈ L^∞(𝕋)`, which holds because `Ψ` is integrable
  and has absolutely summable Fourier coefficients `cw m`;
* `Work.KMTAreas.A7Hi.winConvRep_ftLp_ae` — the convolution theorem
  `𝓕(T_m v) = Ψ · 𝓕v` on the circle.

The rest of the argument (the frequency support of the modulated input, the separation geometry
of the arcs, and the a.e. vanishing of the product) is in this file.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Work.KMTAreas.A7Hi

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "CircB" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-! ## The geometry of the arcs -/

/-- The `arcSet` transport: `y + α` lies in the `ε`-arc around `β` iff `y` lies in the `ε`-arc
around `β - α`. -/
lemma arcSet_add_transport (y α β : Circ) (ε : ℝ) :
    y + α ∈ Work.BourgainPlan.IonescuWainger.arcSet β ε ↔
      y ∈ Work.BourgainPlan.IonescuWainger.arcSet (β - α) ε := by
  simp only [Work.BourgainPlan.IonescuWainger.arcSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    have h' : y = β + (θ : Circ) - α := eq_sub_iff_add_eq.mpr h
    rw [h']; abel
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    rw [h]; abel

/-- The norm of a real number viewed on the circle is at most its absolute value. -/
lemma norm_coe_circle_le_abs (x : ℝ) : ‖(x : Circ)‖ ≤ |x| := by
  by_cases hx : |x| ≤ 1 / 2
  · have hx' : |x| ≤ |(1:ℝ)| / 2 := by rw [abs_one]; norm_num; linarith
    exact le_of_eq ((AddCircle.norm_coe_eq_abs_iff 1 (x := x) one_ne_zero).mpr hx')
  · have h1 : ‖(x : Circ)‖ ≤ |(1:ℝ)| / 2 := AddCircle.norm_le_half_period 1 one_ne_zero
    have h2 : 1 / 2 < |x| := lt_of_not_ge hx
    rw [abs_one] at h1
    linarith

/-- **The separation of the arcs.**  If the `δ`-arcs around the points of `A` are `8δ`-separated,
then a point of the `2δ`-arc around `0` which is *not* in the `δ`-arc around `0` lies in none of
the shifted arcs `arcSet (β - α) δ`, `β ∈ A`. -/
lemma notMem_iUnion_arcSet_sub_of_separated
    (A : Finset CircB) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (α : CircB) (hα : α ∈ A) (ξ : CircB)
    (hδmem : ξ ∉ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (h2 : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ)) :
    ξ ∉ ⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet (β - α) δ := by
  intro hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨β, hβ, hmemβ⟩ := hmem
  rcases eq_or_ne β α with rfl | hne
  · exact hδmem (by simpa using hmemβ)
  · rcases hmemβ with ⟨θ₁, hθ₁, hξ₁⟩
    rcases h2 with ⟨θ₂, hθ₂, hξ₂⟩
    have hβα : β - α = ((θ₂ - θ₁ : ℝ) : CircB) := by
      have h1 : β - α + (θ₁ : CircB) = (θ₂ : CircB) := by rw [← hξ₁, hξ₂, zero_add]
      have h2' : β - α = (θ₂ : CircB) - (θ₁ : CircB) := eq_sub_iff_add_eq.mpr h1
      rw [h2']; norm_cast
    have hnorm : ‖β - α‖ ≤ 3 * δ := by
      rw [hβα]
      have h3 : ‖((θ₂ - θ₁ : ℝ) : CircB)‖ ≤ |θ₂ - θ₁| := norm_coe_circle_le_abs (θ₂ - θ₁)
      have h4 : |θ₂ - θ₁| ≤ |θ₂| + |θ₁| := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [le_abs_self θ₂, neg_abs_le θ₂, le_abs_self θ₁, neg_abs_le θ₁]
      have h5 : |θ₂| ≤ 2 * δ := by
        have := abs_nonneg θ₂; linarith
      have h6 : |θ₁| ≤ δ := hθ₁
      linarith
    have h7 : 8 * δ ≤ ‖α - β‖ := hsep α hα β hβ (Ne.symm hne)
    rw [norm_sub_rev] at h7
    linarith

/-! ## The frequency support of the modulated input -/

/-- The modulation `winModRep (-α) u = M_{-α} u` of an input band-limited to
`⋃_{β ∈ A} arcSet β δ` is band-limited to the shifted union `⋃_{β ∈ A} arcSet (β - α) δ`. -/
lemma hasFreqSupport_winModRep_sub {A : Finset CircB} {δ : ℝ} {u : ℤ → ℂ} (hu : Memℓp u 2)
    (huE : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet β δ))
    (α : Circ) :
    ∃ hv : Memℓp (Work.KMTAreas.A7Rep.winModRep (-α) u) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7Rep.winModRep (-α) u) hv
        (⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet (β - α) δ) := by
  have hv_eq : Work.KMTAreas.A7Rep.winModRep (-α) u
      = Work.BourgainPlan.IonescuWainger.modSeq u α := by
    funext x
    simp only [Work.KMTAreas.A7Rep.winModRep, Work.BourgainPlan.IonescuWainger.modSeq]
    rw [Work.KMTAreas.A7Rep.fourier_apply_neg_rep]
    ring
  refine ⟨hv_eq ▸ Work.BourgainPlan.IonescuWainger.memℓp_modSeq hu α, ?_⟩
  have hvmod : Memℓp (Work.BourgainPlan.IonescuWainger.modSeq u α) 2 :=
    Work.BourgainPlan.IonescuWainger.memℓp_modSeq hu α
  have hsupp_mod : Work.BourgainPlan.IonescuWainger.HasFreqSupport
      (Work.BourgainPlan.IonescuWainger.modSeq u α) hvmod
      {x : CircB | x + α ∈ ⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet β δ} :=
    Work.BourgainPlan.IonescuWainger.hasFreqSupport_modSeq hu huE α
  have hft : (Work.BourgainPlan.IonescuWainger.ftLp (Work.KMTAreas.A7Rep.winModRep (-α) u)
        (hv_eq ▸ hvmod) : Circ → ℂ)
      = (Work.BourgainPlan.IonescuWainger.ftLp
          (Work.BourgainPlan.IonescuWainger.modSeq u α) hvmod : Circ → ℂ) := by
    rw [Work.BourgainPlan.IonescuWainger.ftLp_congr_memℓp hv_eq _ hvmod]
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hsupp_mod ⊢
  filter_upwards [hsupp_mod] with ξ hξ hmem
  rw [hft]
  refine hξ fun hc => hmem ?_
  simp only [Set.mem_iUnion] at hc ⊢
  obtain ⟨β, hβ, hβmem⟩ := hc
  exact ⟨β, hβ, (arcSet_add_transport ξ α β δ).mp hβmem⟩

/-! ## The main theorem -/

theorem windowEnvelopesHasFreqSupport (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (δ : ℝ) (hδ : 0 < δ)
    (hmsup : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize m θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hmplat : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
      Work.Analysis.IonescuWainger.periodize m θ = 1)
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (hsep : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (u : ℤ → ℂ) (hu : Memℓp u 2)
    (huE : Work.BourgainPlan.IonescuWainger.HasFreqSupport u hu
      (⋃ α ∈ A, Work.BourgainPlan.IonescuWainger.arcSet α δ))
    (α : Work.Analysis.IonescuWainger.Circle) (hα : α ∈ A) :
    ∃ hh : Memℓp (Work.KMTAreas.A7Rep.winConvRep m
        (Work.KMTAreas.A7Rep.winModRep (-α) u)) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTAreas.A7Rep.winConvRep m (Work.KMTAreas.A7Rep.winModRep (-α) u)) hh
        (Work.BourgainPlan.IonescuWainger.arcSet 0 δ) := by
  -- the multiplier `Ψ = periodize m` is a.e. bounded
  have hΨ : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize m) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := periodizeMemLpTop hm hmsum
  -- the band-limited modulated input
  obtain ⟨hv, hsuppv⟩ := hasFreqSupport_winModRep_sub hu huE α
  -- the convolution theorem
  obtain ⟨hw, hftw⟩ := winConvRep_ftLp_ae m hm hΨ hv
  refine ⟨hw, ?_⟩
  -- on the `δ`-arc around `0` nothing can survive
  simp only [Work.BourgainPlan.IonescuWainger.HasFreqSupport] at hsuppv ⊢
  filter_upwards [hftw, hsuppv] with ξ hftwξ hsuppvξ hmem
  rw [hftwξ]
  by_cases hper : Work.Analysis.IonescuWainger.periodize m ξ = 0
  · rw [hper, zero_mul]
  · have h2δ : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ) := hmsup ξ hper
    have hsepξ : ξ ∉ ⋃ β ∈ A, Work.BourgainPlan.IonescuWainger.arcSet (β - α) δ :=
      notMem_iUnion_arcSet_sub_of_separated A δ hδ hsep α hα ξ hmem h2δ
    rw [hsuppvξ hsepξ, mul_zero]

end

end Work.KMTAreas.A7Hi
