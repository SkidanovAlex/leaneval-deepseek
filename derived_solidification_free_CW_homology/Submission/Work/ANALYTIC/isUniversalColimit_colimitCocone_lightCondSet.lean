import Mathlib
import Submission.Work.ANALYTIC.isUniversalColimit_colimitCocone_functorCategory

namespace Work.ANALYTIC

open CategoryTheory CategoryTheory.Limits

/-- **Small coproducts in `LightCondSet` are universal** (they are stable under pullback).

Route.  Write `J := coherentTopology LightProfinite.{0}`, `Gl := presheafToSheaf J (Type 0)` and
`Gr := sheafToPresheaf J (Type 0)`, with adjunction `sheafificationAdjunction J (Type 0)`
(`Gr` is full and faithful).  By
`isUniversalColimit_colimitCocone_functorCategory` applied to `C := LightProfinite.{0}ᵒᵖ` and to
the functor `F ⋙ Gr`, the cocone `colimit.cocone (F ⋙ Gr)` in presheaves is universal, so
`IsUniversalColimit.map_reflective` gives that
`Gl.mapCocone (colimit.cocone (F ⋙ Gr))` is universal in `LightCondSet`; the required instances
are `HasSheafify J (Type 0)`, `PreservesFiniteLimits (presheafToSheaf J (Type 0))`, the full and
faithful instance for `Gr` and `HasPullbacks (LightProfinite.{0}ᵒᵖ ⥤ Type 0)`.
Finally `IsUniversalColimit.precompose_isIso` along the natural isomorphism
`Discrete.functor F ⟶ Discrete.functor F ⋙ Gr ⋙ Gl` given by the inverse components of the counit
(an isomorphism since `Gr` is fully faithful) and `IsUniversalColimit.of_iso` (the chosen cocone
`colimit.cocone F` is a colimit cocone by `colimit.isColimit F`, so it is isomorphic to the
transported one) produce the stated conclusion. -/
theorem isUniversalColimit_colimitCocone_lightCondSet {ι : Type} {F : CategoryTheory.Functor (CategoryTheory.Discrete ι) LightCondSet.{0}} [CategoryTheory.Limits.HasColimit F] : CategoryTheory.IsUniversalColimit (CategoryTheory.Limits.colimit.cocone F) := by
  let J := coherentTopology LightProfinite.{0}
  let Gl := presheafToSheaf J (Type 0)
  let Gr := sheafToPresheaf J (Type 0)
  have adj : Gl ⊣ Gr := sheafificationAdjunction J (Type 0)
  -- Step 1: coproducts in the presheaf category `LightProfinite.{0}ᵒᵖ ⥤ Type` are universal.
  have h₁ : IsUniversalColimit (colimit.cocone (F ⋙ Gr)) :=
    Work.ANALYTIC.isUniversalColimit_colimitCocone_functorCategory
  -- Step 2: `map_reflective` transports universality along the reflection `Gl ⊣ Gr`.
  have h₂ : IsUniversalColimit (Gl.mapCocone (colimit.cocone (F ⋙ Gr))) :=
    IsUniversalColimit.map_reflective adj h₁
  -- Step 3: transport along the natural isomorphism `F ≅ (F ⋙ Gr) ⋙ Gl` whose components are the
  -- inverses of the counit components (an isomorphism since `Gr` is fully faithful).
  -- (the instance `IsIso adj.counit` is found by typeclass search, since `Gr` is fully faithful)
  let αIso : F ≅ (F ⋙ Gr) ⋙ Gl :=
    F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit).symm ≪≫
      (Functor.associator F Gr Gl).symm
  have h₃ : IsUniversalColimit
      ((Cocone.precompose αIso.hom).obj (Gl.mapCocone (colimit.cocone (F ⋙ Gr)))) :=
    IsUniversalColimit.precompose_isIso αIso.hom h₂
  -- Step 4: the transported cocone is a colimit cocone over `F`, hence isomorphic to
  -- `colimit.cocone F`.
  refine IsUniversalColimit.of_iso h₃ (Cocone.ext
    (h₃.isColimit.coconePointUniqueUpToIso (colimit.isColimit F))
    (fun j => IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j))

end Work.ANALYTIC
