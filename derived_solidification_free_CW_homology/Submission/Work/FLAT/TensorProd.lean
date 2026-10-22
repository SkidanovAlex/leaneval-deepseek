import Submission.Work.FLAT.Setup

/-!
# AREA FLAT — the tensor product in `LightCondSet` is the cartesian product

The monoidal structure on `LightCondSet` (sheaves of types on the coherent site) is the cartesian
one: with `fst`/`snd` the projections of the monoidal product, `CartesianMonoidalCategory`
provides an `IsLimit` for the corresponding binary fan, so `A ⊗ B` is a product of `A` and `B`.
This file records the resulting comparison isomorphism with the standard categorical product
`A ⨯ B` provided by Mathlib (`Limits.prod`), used to translate the strong-monoidality of `ℤ[-]`
into the form `ℤ[A × B] ≅ ℤ[A] ⊗ ℤ[B]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.FLAT

noncomputable section

/-- The tensor product in `LightCondSet` is the cartesian product. -/
noncomputable def tensorIsoProd (A B : LightCondSet.{0}) : A ⊗ B ≅ A ⨯ B :=
  IsLimit.conePointUniqueUpToIso
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct A B)
    (limit.isLimit (pair A B))

/-- The light profinite set `S` is sent to the light condensed set `S.toCondensed` by the functor
`lightProfiniteToLightCondSet = J.yoneda`, whose underlying presheaf is `Hom(-, S)`.  Since
`J.yoneda` preserves limits, the product of `S.toCondensed` and `T.toCondensed` in `LightCondSet`
is the condensed set on the product `S ⨯ T`. -/
noncomputable def yonedaProdIso (S T : LightProfinite.{0}) :
    (coherentTopology LightProfinite.{0}).yoneda.obj S ⊗
        (coherentTopology LightProfinite.{0}).yoneda.obj T ≅
      (coherentTopology LightProfinite.{0}).yoneda.obj (S ⨯ T) :=
  tensorIsoProd _ _ ≪≫
    (HasLimit.isoOfNatIso (pairComp S T (coherentTopology LightProfinite.{0}).yoneda)).symm ≪≫
    ((isLimitOfPreserves (coherentTopology LightProfinite.{0}).yoneda
        (limit.isLimit (pair S T))).conePointUniqueUpToIso
      (limit.isLimit (pair S T ⋙ (coherentTopology LightProfinite.{0}).yoneda))).symm

/-- `S.toCondensed ⊗ T.toCondensed ≅ (S ⨯ T).toCondensed`. -/
noncomputable def toCondensedTensorIso (S T : LightProfinite.{0}) :
    S.toCondensed ⊗ T.toCondensed ≅ (S ⨯ T).toCondensed :=
  yonedaProdIso S T

end

end Work.FLAT
