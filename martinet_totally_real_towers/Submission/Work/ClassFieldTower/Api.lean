import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.exists_maximalUnramifiedProP

/-!
# `Work.ClassFieldTower.Api` -- small interface lemmas

* `hasMinimalPresentation_of_mulEquiv`: `HasMinimalPresentation` transports across group
  isomorphisms (so a presentation of an abstract presentation group can be moved to `G_∅`);
* `nonempty_maximalUnramifiedProP`: the maximal unramified pro-`p` extension exists
  (restatement of the delegated existence theorem).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **`HasMinimalPresentation` transports across a group isomorphism.** -/
theorem hasMinimalPresentation_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {d r : ℕ} (h : HasMinimalPresentation G d r) : HasMinimalPresentation H d r := by
  classical
  obtain ⟨α, iα, iDα, rel, hcard, hrel, ⟨eG⟩, hmin⟩ := h
  refine ⟨α, iα, iDα, rel, hcard, hrel, ⟨e.symm.trans eG⟩, ?_⟩
  intro S hS
  have hgen : Subgroup.closure (((S.image (⇑e.symm) : Finset G)) : Set G) = ⊤ := by
    have hm : Subgroup.closure (⇑e.symm '' (S : Set H)) = ⊤ := by
      have h1 : Subgroup.map (e.symm : H →* G) (Subgroup.closure (S : Set H)) = ⊤ := by
        rw [hS, Subgroup.map_top_of_surjective _ e.symm.surjective]
      rwa [MonoidHom.map_closure (e.symm : H →* G) (S : Set H)] at h1
    rw [Finset.coe_image]
    exact hm
  have hle := hmin (S.image (⇑e.symm)) hgen
  rwa [Finset.card_image_of_injective _ e.symm.injective] at hle

/-- **The maximal unramified pro-`p` extension of a number field exists.** -/
theorem nonempty_maximalUnramifiedProP (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] : Nonempty (MaximalUnramifiedProP.{0} F p) :=
  exists_maximalUnramifiedProP F p

end Work.ClassFieldTower
