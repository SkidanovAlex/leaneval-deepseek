import Mathlib
import Submission.Work.DISC.Defs

namespace Work.DISC

open CategoryTheory Limits LightProfinite LightCondensed Opposite

/-- Naturality of the comparison isomorphism `Hom(ℤ[S], A) ≅ A(S)` in the light profinite set
`S`: precomposition with `ℤ[f]` corresponds to restriction along `f`.

This is the composite of the naturality of the transposition of the free–forgetful adjunction
`free ⊣ forget` (in its source variable) with the naturality of the Yoneda equivalence for a
subcanonical topology. -/
theorem homFreeEquiv_naturality (S S' : LightProfinite.{0}) (f : S ⟶ S') (A : LightCondAb)
    (g : Work.DISC.zfree S' ⟶ A) :
    Work.DISC.homFreeEquiv S A (CategoryTheory.CategoryStruct.comp (Work.DISC.zfreeFunctor.map f) g) =
      A.obj.map (Quiver.Hom.op f) (Work.DISC.homFreeEquiv S' A g) := by
  show (coherentTopology LightProfinite).yonedaEquiv
      ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj S) A
        ((free ℤ).map (lightProfiniteToLightCondSet.map f) ≫ g)) =
    ((LightCondensed.forget ℤ).obj A).obj.map (Quiver.Hom.op f)
      ((coherentTopology LightProfinite).yonedaEquiv
        ((freeForgetAdjunction ℤ).homEquiv (lightProfiniteToLightCondSet.obj S') A g))
  rw [Adjunction.homEquiv_naturality_left]
  exact (GrothendieckTopology.yonedaEquiv_naturality (J := coherentTopology LightProfinite) _ f).symm

end Work.DISC
