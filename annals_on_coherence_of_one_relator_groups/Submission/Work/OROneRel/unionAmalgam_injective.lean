import Mathlib
import Submission.Work.OROneRel.presentedGroup_union_amalgam

namespace Work.OROneRel

/-- **The `π₁` of one piece of a union of two `2`-complexes injects into the `π₁` of the union,
provided the two amalgamating maps are injective and the two pieces cover the edge set.**  This is
the composition of the isomorphism `Work.OROneRel.presentedGroup_union_amalgam` with Mathlib's
`Monoid.PushoutI.of_injective`; it is the atomic step out of which the line-amalgam (Britton normal
form) argument is built.  Suggested proof: `presentedMap (incVal E₁) ugSubset₁` equals
`ugOut ∘ (Monoid.PushoutI.of false)` (`Work.OROneRel.ugOut_of_false`), the map `ugOut` is injective
because it is inverse to `ugIn` (`Work.OROneRel.ugIn_comp_ugOut`), and `Monoid.PushoutI.of false` is
injective by `Monoid.PushoutI.of_injective` applied to `hφ`. -/
theorem unionAmalgam_injective {E : Type*} (E₁ E₂ : Set E)
    (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂)
    (S₁ : Set (FreeGroup ↥E₁)) (S₂ : Set (FreeGroup ↥E₂)) (S₀ : Set (FreeGroup ↥(E₁ ∩ E₂)))
    (h₁ : FreeGroup.map (Work.OROneRel.inc₁ E₁ E₂) '' S₀ ⊆ S₁)
    (h₂ : FreeGroup.map (Work.OROneRel.inc₂ E₁ E₂) '' S₀ ⊆ S₂)
    (hφ : ∀ i, Function.Injective
      (Work.OROneRel.UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂ i)) :
    Function.Injective
      (Work.OROneRel.presentedMap (Work.OROneRel.incVal E₁)
        (Work.OROneRel.ugSubset₁ E₁ E₂ S₁ S₂)) := by
  -- The canonical map of the first vertex group into the amalgam is injective, by Mathlib.
  have hof : Function.Injective
      (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false) :=
    Monoid.PushoutI.of_injective hφ false
  -- The map out of the amalgam is injective, since `ugIn` is a left inverse of it.
  have hleft : Function.LeftInverse (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE)
      (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) := by
    intro x
    have h := DFunLike.congr_fun (ugIn_comp_ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) x
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  have hout : Function.Injective (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) := hleft.injective
  -- The map `π₁(A) → π₁(Γ)` is `ugOut ∘ (of false)`, by `ugOut_of_false`.
  intro a b hab
  exact hof (hout (by rw [ugOut_of_false, hab, ugOut_of_false]))

end Work.OROneRel
