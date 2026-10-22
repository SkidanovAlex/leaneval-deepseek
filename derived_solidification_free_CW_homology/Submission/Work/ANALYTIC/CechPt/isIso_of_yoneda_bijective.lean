/-
# Isomorphisms of light condensed sets are detected by the light profinite test objects

A morphism `φ : F ⟶ G` of light condensed sets is an isomorphism as soon as, for every light
profinite set `S`, precomposition with `φ` defines a bijection
`(toCondensed S ⟶ F) ≃ (toCondensed S ⟶ G)`.

The proof is the Yoneda lemma for a subcanonical site (`GrothendieckTopology.yonedaEquiv`),
applied to the coherent topology on `LightProfinite`, whose Yoneda embedding is
`LightProfinite.toCondensed`.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

open CategoryTheory Opposite

/--
If precomposition with `φ` is a bijection on morphisms out of every light profinite test object,
then `φ` is an isomorphism.
-/
theorem isIso_of_yoneda_bijective {F G : LightCondSet.{0}} (φ : F ⟶ G)
    (h : ∀ S : LightProfinite.{0}, Function.Bijective
      (fun c : LightProfinite.toCondensed S ⟶ F => CategoryTheory.CategoryStruct.comp c φ)) :
    CategoryTheory.IsIso φ := by
  let J : GrothendieckTopology LightProfinite.{0} := coherentTopology LightProfinite.{0}
  haveI : J.Subcanonical := inferInstance
  -- Yoneda for the subcanonical site `LightProfinite`: sections of `F` over `S` are morphisms
  -- `toCondensed S ⟶ F`, compatibly with postcomposition.
  have hcomp : ∀ S : LightProfinite.{0}, Function.Bijective ((φ.hom).app (op S)) := by
    intro S
    have hS := h S
    have key : ((φ.hom).app (op S)) =
        (fun x : F.obj.obj (op S) => J.yonedaEquiv ((fun c : J.yoneda.obj S ⟶ F => c ≫ φ)
          (J.yonedaEquiv.symm x))) := by
      funext x
      simp only [GrothendieckTopology.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [key]
    exact (J.yonedaEquiv.bijective).comp (hS.comp (J.yonedaEquiv.symm.bijective))
  -- A natural transformation of type-valued presheaves is invertible once it is
  -- objectwise bijective.
  have hmap : IsIso ((sheafToPresheaf J (Type 0)).map φ) := by
    change IsIso φ.hom
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact (isIso_iff_bijective _).mpr (hcomp X.unop)
  -- The forgetful functor to presheaves is fully faithful, hence reflects isomorphisms.
  haveI := hmap
  exact Functor.ReflectsIsomorphisms.reflects (sheafToPresheaf J (Type 0)) φ

end Work.ANALYTIC.CechPt
