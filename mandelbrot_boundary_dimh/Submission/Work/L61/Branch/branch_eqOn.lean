import Mathlib
import Submission.Work.L61.Basic

/-!
# Lemma 6.1 (Shishikura §6) — uniqueness of inverse branches of `g`

The pushed-down horn map `g = Work.L61.g d` (for a horn datum `hd`) is a covering map over the
complement of the critical orbit `Kset d hd` (hypothesis `hcov`).  Consequently two continuous
lifts `ψ₁ ψ₂` of a map `f` with `f z ∉ Kset` that agree at a single point of a preconnected open
set `U` agree on all of `U`.

This is the standard uniqueness of lifts: for a covering map `p`, a locally injective separated
map (`IsCoveringMap.isSeparatedMap`, `IsCoveringMap.isLocalHomeomorph`), the agreement locus of
two lifts is clopen, so on a preconnected domain it is either empty or everything
(`IsSeparatedMap.eq_of_comp_eq`).

The relevant covering is not `g` on all of `ℂ` but `g` restricted to
`{ζ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd}`, on the base `(Kset d hd)ᶜ`.  Since the lifts satisfy
`g (ψᵢ z) = f z ∉ Kset`, they take their values in the further restricted total space
`coverSpace d hd = p ⁻¹' (Kset)ᶜ`, over which `p` is a genuine covering map.
-/

namespace Work.L61.Branch

open Set Function Topology
open Work.L61 MandelDim

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

noncomputable section

/-- The total space on which `g` is a covering: points of `gdom` at which `g` does not take the
critical value `critVal hd`. -/
abbrev coverTotal (d : ParabData f₀ D₀) (hd : HornData d) : Type :=
  {ζ : ℂ // ζ ∈ gdom d hd ∧ g d ζ ≠ critVal hd}

/-- The pushed-down horn map as a map on its total space. -/
abbrev coverMap (d : ParabData f₀ D₀) (hd : HornData d) : coverTotal d hd → ℂ := fun ζ => g d ζ

/-- The part of the total space lying over `(Kset d hd)ᶜ`: the space in which the lifts of
`branch_eqOn` actually take their values. -/
abbrev coverSpace (d : ParabData f₀ D₀) (hd : HornData d) : Type :=
  {ζ : coverTotal d hd // g d ζ ∈ (Kset d hd)ᶜ}

/-- The covering map restricted to the preimage of `(Kset d hd)ᶜ`. -/
abbrev coverRestr (d : ParabData f₀ D₀) (hd : HornData d) :
    coverSpace d hd → {y : ℂ // y ∈ (Kset d hd)ᶜ} := fun ζ => ⟨g d ζ, ζ.2⟩

/-- The covering hypothesis of Lemma 6.1 gives a covering map of subtype spaces, over the base
`(Kset d hd)ᶜ`. -/
theorem isCoveringMap_coverRestr {d : ParabData f₀ D₀} (hd : HornData d)
    (hcov : IsCoveringMapOn (coverMap d hd) (Kset d hd)ᶜ) :
    IsCoveringMap (coverRestr d hd) :=
  hcov.isCoveringMap_restrictPreimage

set_option linter.unusedVariables false in
/-- **Uniqueness of the inverse branch of `g`** (Lemma 6.1, uniqueness part).  Two continuous
lifts of the same map `f : U → (Kset d hd)ᶜ` to `gdom`, defined on a preconnected open `U`, that
agree at one point of `U`, agree on all of `U`. -/
theorem branch_eqOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} (hd : MandelDim.HornData d)
    (hcov : IsCoveringMapOn (fun ζ : {ζ : ℂ // ζ ∈ Work.L61.gdom d hd ∧ Work.L61.g d ζ ≠ Work.L61.critVal hd} =>
      Work.L61.g d ζ) (Work.L61.Kset d hd)ᶜ)
    {U : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U) {f : ℂ → ℂ}
    (hfK : ∀ z ∈ U, f z ∉ Work.L61.Kset d hd) {ψ₁ ψ₂ : ℂ → ℂ}
    (h₁ : ∀ z ∈ U, Work.L61.g d (ψ₁ z) = f z) (h₂ : ∀ z ∈ U, Work.L61.g d (ψ₂ z) = f z)
    (hc₁ : ContinuousOn ψ₁ U) (hc₂ : ContinuousOn ψ₂ U)
    (hψg : ∀ z ∈ U, ψ₁ z ∈ Work.L61.gdom d hd ∧ ψ₂ z ∈ Work.L61.gdom d hd)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (heq : ψ₁ z₀ = ψ₂ z₀) : Set.EqOn ψ₁ ψ₂ U := by
  classical
  -- `g` is a covering map of subtypes over `(Kset)ᶜ`
  have hq : IsCoveringMap (coverRestr d hd) :=
    isCoveringMap_coverRestr hd (show IsCoveringMapOn (coverMap d hd) (Kset d hd)ᶜ from hcov)
  -- the two lifts take their values in the total space `coverTotal d hd`
  have hmem1 : ∀ z ∈ U, ψ₁ z ∈ gdom d hd ∧ g d (ψ₁ z) ≠ critVal hd := by
    intro z hz
    refine ⟨(hψg z hz).1, ?_⟩
    rw [h₁ z hz]
    intro h
    exact hfK z hz (by rw [h]; exact critVal_mem_Kset d hd)
  have hmem2 : ∀ z ∈ U, ψ₂ z ∈ gdom d hd ∧ g d (ψ₂ z) ≠ critVal hd := by
    intro z hz
    refine ⟨(hψg z hz).2, ?_⟩
    rw [h₂ z hz]
    intro h
    exact hfK z hz (by rw [h]; exact critVal_mem_Kset d hd)
  -- ... and even over `(Kset)ᶜ`, since `g (ψᵢ z) = f z ∉ Kset`
  have hk1 : ∀ z ∈ U, g d (ψ₁ z) ∈ (Kset d hd)ᶜ := fun z hz => by
    rw [h₁ z hz]; exact hfK z hz
  have hk2 : ∀ z ∈ U, g d (ψ₂ z) ∈ (Kset d hd)ᶜ := fun z hz => by
    rw [h₂ z hz]; exact hfK z hz
  -- them as continuous maps `U → coverSpace d hd`
  let Ψ₁ : U → coverSpace d hd :=
    fun z => ⟨⟨ψ₁ z, (hmem1 z z.2).1, (hmem1 z z.2).2⟩, hk1 z z.2⟩
  let Ψ₂ : U → coverSpace d hd :=
    fun z => ⟨⟨ψ₂ z, (hmem2 z z.2).1, (hmem2 z z.2).2⟩, hk2 z z.2⟩
  have hcΨ₁ : Continuous Ψ₁ :=
    Continuous.subtype_mk (Continuous.subtype_mk hc₁.domRestrict (fun z => hmem1 z z.2))
      (fun z => hk1 z z.2)
  have hcΨ₂ : Continuous Ψ₂ :=
    Continuous.subtype_mk (Continuous.subtype_mk hc₂.domRestrict (fun z => hmem2 z z.2))
      (fun z => hk2 z z.2)
  -- both are lifts of the same map
  have hcomp : coverRestr d hd ∘ Ψ₁ = coverRestr d hd ∘ Ψ₂ := by
    funext z
    refine Subtype.ext ?_
    simp only [Function.comp_apply, coverRestr, Ψ₁, Ψ₂, h₁ z z.2, h₂ z z.2]
  have hz₀eq : Ψ₁ ⟨z₀, hz₀⟩ = Ψ₂ ⟨z₀, hz₀⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUpc
  have hfinal : Ψ₁ = Ψ₂ := hq.isSeparatedMap.eq_of_comp_eq hq.isLocalHomeomorph.isLocallyInjective
    hcΨ₁ hcΨ₂ hcomp ⟨z₀, hz₀⟩ hz₀eq
  intro z hz
  have h := congr_fun hfinal ⟨z, hz⟩
  exact congrArg (fun w : coverSpace d hd => ((w : coverTotal d hd) : ℂ)) h

end

end Work.L61.Branch
