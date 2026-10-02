import Mathlib
import Submission.Work.TangentClasses.DiscProj
import Submission.Work.TangentClasses.HMap_homotopic
import Submission.Work.TangentClasses.homotopic_section_comp_proj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# The canonical geometric input, and the unconditional identification `p₁(TX) = cappedPontryaginClass`

`Submission/Work/TangentClasses/DiscProj.lean` shows that the zero section `s` of the disc bundle
`D(ξ) = Vk (-2)` splits the bundle projection `π` on the *other* side (`π ∘ s = id`), so that
`π^*` is injective.  `Submission/Work/TangentClasses/homotopic_section_comp_proj.lean` (delegated)
supplies the remaining half of the homotopy equivalence: the fibrewise scaling by `t ∈ [0,1]` is a
homotopy from `s ∘ π` to the identity of `D(ξ)` — the deformation retraction of the disc bundle
onto its zero section.

Consequently `π^* : H^n(S⁴;ℤ) → H^n(D(ξ);ℤ)` is **surjective** in every degree
(`surjective_HMap_discProj`), and the geometric input of `Capped.lean` can be built canonically, with
the *positive* normalisation of the generator (`discTangentSplitting`).  For that canonical input the
identification of the first Pontryagin class of the tangent bundle with the class constructed by the
characteristic-classes chapter is **unconditional**:

  `p1Tangent F hF discTangentSplitting = Work.Milnor.cappedPontryaginClass F hF`

(`p1Tangent_discTangentSplitting`).  So the only input of the critical computation is the geometric
identification `TX|_{{D(ξ)}} ≅ π^*(TS⁴ ⊕ ξ)`, encoded in `DiscTangentSplitting`.
-/

namespace Work.TangentClasses

open CategoryTheory
open Work.CharacteristicClasses

noncomputable section

/-- **The pullback along the bundle projection of the disc bundle is surjective** in every degree:
`π` is a homotopy inverse of the zero section `s` (the deformation retraction
`homotopic_section_comp_proj` and the identity `π ∘ s = id`). -/
theorem surjective_HMap_discProj (n : ℕ) : Function.Surjective (HMap discProj n).hom := by
  intro z
  refine ⟨(HMap discSection n).hom z, ?_⟩
  obtain ⟨Hh⟩ := homotopic_section_comp_proj
  have key : HMap (discSection.comp discProj) n = 𝟙 (H n DiscSpace) := by
    rw [HMap_homotopic ⟨Hh⟩ n, HMap_id]
  have key2 := HMap_comp discProj discSection n
  rw [key] at key2
  have h2 := congrArg (fun f : H n DiscSpace ⟶ H n DiscSpace => f.hom z) key2
  simpa using h2.symm

/-- **The bundle projection of the disc bundle is a homotopy equivalence** (it has the zero
section as a two-sided homotopy inverse): its induced map on cohomology is bijective in every
degree. -/
theorem bijective_HMap_discProj (n : ℕ) : Function.Bijective (HMap discProj n).hom :=
  ⟨injective_HMap_discProj n, surjective_HMap_discProj n⟩

/-- Consequently the pullback along the bundle projection is an isomorphism of cohomology groups in
every degree (both sides are computed in the workspace's cochain model). -/
theorem isIso_HMap_discProj (n : ℕ) : IsIso (HMap discProj n) := by
  haveI : Mono (HMap discProj n) :=
    (ModuleCat.mono_iff_injective _).mpr (injective_HMap_discProj n)
  haveI : Epi (HMap discProj n) :=
    (ModuleCat.epi_iff_surjective _).mpr (surjective_HMap_discProj n)
  exact isIso_of_mono_of_epi _

/-- **The canonical geometric input for `p₁(TX)`**: the honest bundle projection
`π : D(ξ) → S⁴` of the disc bundle, together with a generator `G` of `H⁴(S⁴;ℤ)` whose pullback
along `π` is the chapter's generator `τ` of `H⁴(D(ξ);ℤ) ≅ ℤ`.  The class `G` exists by
`surjective_HMap_discProj`. -/
noncomputable def discTangentSplitting : DiscTangentSplitting where
  proj := discProj
  G := Classical.choose (surjective_HMap_discProj 4 Work.Milnor.tauD)
  G_pullback := Or.inl (Classical.choose_spec (surjective_HMap_discProj 4 Work.Milnor.tauD))

/-- The canonical splitting has the positive normalisation. -/
theorem discTangentSplitting_G_pullback :
    (HMap discTangentSplitting.proj 4).hom discTangentSplitting.G = Work.Milnor.tauD :=
  Classical.choose_spec (surjective_HMap_discProj 4 Work.Milnor.tauD)

/-- **THE CRITICAL COMPUTATION, UNCONDITIONALLY.**  For the canonical geometric input — the honest
bundle projection of the disc bundle and the generator normalised so that its pullback is `τ` —
the first Pontryagin class `p₁(TX)` constructed in this chapter is *equal* to
`Work.Milnor.cappedPontryaginClass F hF`, the class the characteristic-classes chapter constructs.

The only input is the geometric identification `TX|_{{D(ξ)}} ≅ π^*(TS⁴ ⊕ ξ)` (encoded in the
`DiscTangentSplitting`), and the value `p₁(ξ) = 6` of the characteristic-classes chapter. -/
theorem p1Tangent_discTangentSplitting
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) :
    p1Tangent F hF discTangentSplitting = Work.Milnor.cappedPontryaginClass F hF :=
  p1Tangent_eq_cappedPontryaginClass F hF discTangentSplitting discTangentSplitting_G_pullback

/-- The endgame input in coefficient form, for the canonical splitting: **`p₁(TX) = q · x` with
`q ∈ {6, -6}` for every generator `x` of `H⁴(X;ℤ) ≅ ℤ`** — without any hypothesis beyond the
geometric identification. -/
theorem p1Tangent_discTangentSplitting_six
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F)
    (x : H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
    (hx : ∀ z : H 4 (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)), ∃ a : ℤ, z = a • x) :
    ∃ q : ℤ, (q = 6 ∨ q = -6) ∧ p1Tangent F hF discTangentSplitting = q • x :=
  p1Tangent_six F hF discTangentSplitting x hx

end

end Work.TangentClasses
