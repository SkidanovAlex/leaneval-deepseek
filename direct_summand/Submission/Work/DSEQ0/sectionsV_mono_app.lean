import Mathlib
import Submission.Work.DSEQ0.AugDefs

namespace Work.DSEQ0

universe u

open CategoryTheory

theorem sectionsV_mono_app {X : AlgebraicGeometry.Scheme.{u}}
    {M N : AlgebraicGeometry.Scheme.Modules X} (φ : M ⟶ N) [CategoryTheory.Mono φ] (V : X.Opens) :
    Function.Injective (CategoryTheory.ConcreteCategory.hom
      (AlgebraicGeometry.Scheme.Modules.Hom.app φ V)) := by
  -- `(toPresheaf X).map φ` is a monomorphism of presheaves of abelian groups, since the
  -- forgetful functor `toPresheaf X` preserves limits (it is a forgetful functor to presheaves
  -- of abelian groups) and hence monomorphisms.
  haveI h1 : CategoryTheory.Mono
      ((AlgebraicGeometry.Scheme.Modules.toPresheaf X).map φ) :=
    CategoryTheory.Functor.map_mono _ φ
  -- a mono of presheaves is pointwise a mono (`NatTrans.mono_iff_mono_app`), and the component
  -- at `V` is precisely `Hom.app φ V`
  have h2 : CategoryTheory.Mono
      (((AlgebraicGeometry.Scheme.Modules.toPresheaf X).map φ).app (Opposite.op V)) :=
    inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp h2

end Work.DSEQ0
