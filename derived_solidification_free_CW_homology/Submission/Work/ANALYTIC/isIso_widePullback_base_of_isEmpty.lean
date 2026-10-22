import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits in
theorem isIso_widePullback_base_of_isEmpty {C : Type*} [Category C] {J : Type*} [IsEmpty J]
    {Z : C} {X : J → C} (φ : ∀ j, X j ⟶ Z) [HasWidePullback Z X φ] :
    IsIso (WidePullback.base φ) := by
  -- When `J` is empty the wide cospan is the single object `Z` with its identity,
  -- so the wide pullback is `Z` and `base` is an isomorphism.
  refine ⟨WidePullback.lift (𝟙 Z) (fun j => isEmptyElim j) (fun j => isEmptyElim j), ?_, ?_⟩
  · refine WidePullback.hom_ext (arrows := φ) _ _ (fun j => isEmptyElim j) ?_
    simp [WidePullback.lift_base]
  · exact WidePullback.lift_base (arrows := φ) _ _ _

end Work.ANALYTIC
