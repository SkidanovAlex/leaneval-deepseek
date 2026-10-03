import Mathlib

namespace Work.ORLocInd

/-- **Naturality of `PresentedGroup` in the relator.**  An isomorphism of free groups
`e : FreeGroup α ≃* FreeGroup β` maps the one-relator presentation `⟨α | r⟩` isomorphically onto
the one-relator presentation `⟨β | e r⟩` obtained by transporting the (single) relator along `e`.

Since `PresentedGroup rels = FreeGroup α ⧸ Subgroup.normalClosure rels`, this is the quotient
isomorphism induced by `e`; the only input is that a surjection of groups carries the normal
closure of a set onto the normal closure of its image
(`Subgroup.map_normalClosure`). -/
theorem presentedGroup_iso_of_mulEquiv {α β : Type*}
    (e : FreeGroup α ≃* FreeGroup β) (r : FreeGroup α) :
    Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      PresentedGroup ({e r} : Set (FreeGroup β))) := by
  refine ⟨QuotientGroup.congr (Subgroup.normalClosure ({r} : Set (FreeGroup α)))
    (Subgroup.normalClosure ({e r} : Set (FreeGroup β))) e ?_⟩
  rw [Subgroup.map_normalClosure _ (e : FreeGroup α →* FreeGroup β) e.surjective,
    Set.image_singleton]
  rfl

end Work.ORLocInd
