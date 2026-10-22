import Mathlib
import Submission.Work.RESOL.Basic

/-!
# AREA RESOL — the atom skeleton of `LightProfinite`

Every light profinite set is a retract of a member of one fixed *small* family of light profinite
sets.  This is the "skeleton" input used to build small atomic covers of light condensed abelian
groups.

The point is that `LightProfinite` is an essentially small category: Mathlib proves
`EssentiallySmall.{0} LightProfinite.{0}` (via the equivalence with the small category
`LightDiagram'`).  Taking the small category `ι` supplied by that instance and
`S := e.inverse.obj`, every `X` is a retract of `S (e.functor.obj X)` through the unit isomorphism
of the equivalence: the retraction is the inverse of the unit at `X`.
-/

namespace Work.RESOL

theorem exists_atomSkeleton : ∃ (ι : Type) (S : ι → LightProfinite.{0}),
    ∀ X : LightProfinite.{0}, ∃ (i : ι) (e : X ⟶ S i) (r : S i ⟶ X),
      CategoryTheory.CategoryStruct.comp e r = CategoryTheory.CategoryStruct.id X := by
  obtain ⟨ι, hι, ⟨e⟩⟩ :=
    CategoryTheory.EssentiallySmall.equiv_smallCategory (C := LightProfinite.{0})
  exact ⟨ι, fun i => e.inverse.obj i, fun X =>
    ⟨e.functor.obj X, (e.unitIso.app X).hom, (e.unitIso.app X).inv,
      (e.unitIso.app X).hom_inv_id⟩⟩

end Work.RESOL
