import Mathlib

/-!
# Products of sheaves are sheaves

If `Q i` is a sheaf of abelian groups on a topological space `X` for every `i`, then so is the
product presheaf `∏ᶜ Q` (the product being taken in the category of presheaves, i.e. pointwise).

The proof is structural: the sheaf condition is a limit condition (a presheaf is a sheaf iff, for
every covering, the associated multifork is a limit), it is stated for an arbitrary shape by
`ObjectProperty.IsClosedUnderLimitsOfShape (Presheaf.IsSheaf J)` in
`Mathlib/CategoryTheory/Sites/Limits.lean`, and `∏ᶜ Q` is by definition the limit of `Q` over the
discrete index category.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory Limits TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- A product of sheaves (of abelian groups, on a topological space) is a sheaf. -/
theorem isSheaf_pi {X : TopCat.{u}} {ι : Type u} (Q : ι → TopCat.Presheaf AddCommGrpCat.{u} X)
    (hQ : ∀ i, TopCat.Presheaf.IsSheaf (Q i)) :
    TopCat.Presheaf.IsSheaf (∏ᶜ Q) := by
  -- The property of being a sheaf, as an object property of the presheaf category.
  let P : ObjectProperty ((Opens ↑X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    Presheaf.IsSheaf (Opens.grothendieckTopology ↑X)
  -- Sheaves are closed under limits of any shape, in particular over a discrete index category.
  haveI : P.IsClosedUnderLimitsOfShape (Discrete ι) := inferInstance
  -- `∏ᶜ Q` is the limit of the diagram `Q` indexed by `Discrete ι`, whose objects are sheaves.
  have h : P.LimitOfShape (Discrete ι) (∏ᶜ Q) :=
    ObjectProperty.LimitOfShape.limit (Discrete.functor Q) (fun j => hQ j.as)
  exact ObjectProperty.limitsOfShape_le P (Discrete ι) (∏ᶜ Q)
    (ObjectProperty.LimitOfShape.limitsOfShape h)

end Work.DSF1.Sheaf
