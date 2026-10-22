import Mathlib
import Submission.Work.DISC.Defs

/-!
# Naturality of `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S ⊗ T]` in the second variable

The canonical isomorphism `freeTensorIso S T : ℤ[S] ⊗ ℤ[T] ≅ ℤ[S ⊗ T]` of `Work.DISC.Defs`
is the composite of the monoidal structure isomorphism `μ` of `Free ℤ` and the image under
`Free ℤ` of the monoidal structure isomorphism `μ` of `lightProfiniteToLightCondSet`.

Its naturality in `T` is therefore the whiskering-by-`S` naturality of `μ` for both functors:
the two naturality squares `Functor.LaxMonoidal.μ_natural_right` (one in `LightCondSet`, one in
`LightCondAb`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

theorem freeTensorIso_natural (S : LightProfinite.{0}) {T T' : LightProfinite.{0}} (f : T ⟶ T') :
    CategoryTheory.CategoryStruct.comp (Work.DISC.freeTensorIso S T).hom
        (Work.DISC.zfreeFunctor.map (CategoryTheory.MonoidalCategory.whiskerLeft S f)) =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategory.whiskerLeft (Work.DISC.zfree S)
          (Work.DISC.zfreeFunctor.map f))
        (Work.DISC.freeTensorIso S T').hom := by
  have hG := Functor.LaxMonoidal.μ_natural_right lightProfiniteToLightCondSet S f
  have hF := Functor.LaxMonoidal.μ_natural_right (LightCondensed.free (R := ℤ))
      (lightProfiniteToLightCondSet.obj S) (lightProfiniteToLightCondSet.map f)
  simp only [Work.DISC.freeTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.Monoidal.μIso_hom, Work.DISC.zfreeFunctor,
    Functor.comp_obj, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, ← hG, Functor.map_comp, ← Category.assoc, ← hF, Category.assoc]

end Work.DISC
