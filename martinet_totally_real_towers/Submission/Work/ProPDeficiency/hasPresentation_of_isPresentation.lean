import Mathlib
import Submission.Work.ProPDeficiency.Basic

namespace Work.ProPDeficiency

-- File: Submission/Work/ProPDeficiency/hasPresentation_of_isPresentation.lean, namespace `Work.ProPDeficiency`.
-- `HasPresentation G d r` is defined in `Submission.Work.ProPDeficiency.Basic` as
-- `∃ (α : Type) (_ : Fintype α) (rel : Finset (FreeGroup α)),
--    Fintype.card α = d ∧ rel.card = r ∧ IsPresentation α rel G`,
-- where the generator type of the existential lives in `Type` (universe `0`), while
-- `IsPresentation α rel G` (same file) is universe polymorphic.  This result transports a
-- presentation on an arbitrary finite `α` to the standard generators `Fin (Fintype.card α)`:
-- use `Fintype.equivFin α : α ≃ Fin (Fintype.card α)` and the induced isomorphism
-- `FreeGroup.freeGroupCongr`, mapping `rel` to its image and using
-- `MonoidHom.map_closure`/normal-closure transport.
theorem hasPresentation_of_isPresentation {α : Type*} [Fintype α] {rel : Finset (FreeGroup α)}
    {G : Type} [Group G] (h : IsPresentation α rel G) :
    HasPresentation G (Fintype.card α) rel.card := by
  classical
  obtain ⟨f⟩ := h
  -- The standard generators: reindex `α` along `Fintype.equivFin α`.
  set φ : FreeGroup α ≃* FreeGroup (Fin (Fintype.card α)) :=
    FreeGroup.freeGroupCongr (Fintype.equivFin α) with hφ
  -- Reindexing is injective, so it preserves the number of relators.
  have hcard : (rel.image φ : Finset (FreeGroup (Fin (Fintype.card α)))).card = rel.card :=
    Finset.card_image_of_injective _ φ.injective
  -- Reindexing carries the normal closure of `rel` to the normal closure of the image of `rel`.
  have hmap : (Subgroup.normalClosure (rel : Set (FreeGroup α))).map φ.toMonoidHom =
      Subgroup.normalClosure ((rel.image φ : Finset (FreeGroup (Fin (Fintype.card α)))) :
        Set (FreeGroup (Fin (Fintype.card α)))) := by
    rw [Subgroup.map_normalClosure (s := (rel : Set (FreeGroup α))) (f := φ.toMonoidHom)
      φ.surjective]
    congr 1
    exact (Finset.coe_image (s := rel)
      (f := (⇑φ : FreeGroup α → FreeGroup (Fin (Fintype.card α))))).symm
  exact ⟨Fin (Fintype.card α), inferInstance, rel.image φ, Fintype.card_fin _, hcard,
    ⟨f.trans (QuotientGroup.congr (Subgroup.normalClosure (rel : Set (FreeGroup α)))
      (Subgroup.normalClosure ((rel.image φ : Finset (FreeGroup (Fin (Fintype.card α)))) :
        Set (FreeGroup (Fin (Fintype.card α))))) φ hmap)⟩⟩

end Work.ProPDeficiency
