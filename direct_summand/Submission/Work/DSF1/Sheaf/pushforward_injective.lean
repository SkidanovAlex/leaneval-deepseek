import Mathlib

/-!
# Pushforward along an open immersion preserves injectives

For a scheme `X` and an open `W : X.Opens`, the pushforward functor
`Scheme.Modules.pushforward W.ι : W.toScheme.Modules ⥤ X.Modules` is right adjoint to the
restriction functor `Scheme.Modules.restrictFunctor W.ι` (see
`Scheme.Modules.restrictAdjunction`).  A right adjoint whose left adjoint preserves
monomorphisms preserves injective objects
(`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`), and
restriction along an open immersion does preserve monomorphisms, since on the level of
presheaves of modules it is just a pushforward (`SheafOfModules.pushforward`), which is
pointwise the original map.

Hence `pushforward W.ι` sends injective `𝒪_W`-modules to injective `𝒪_X`-modules.

The formalisation is carried out in two general steps:
* `presheafPushforward_preservesMonomorphisms`: pushforward of presheaves of modules
  preserves monomorphisms (monomorphisms in a category of presheaves of modules are
  exactly the pointwise injective maps, `PresheafOfModules.mono_iff_surjective`);
* `sheafPushforward_preservesMonomorphisms`: pushforward of sheaves of modules preserves
  monomorphisms, deduced from the previous point by the fact that the forgetful functor to
  presheaves of modules is faithful and preserves monomorphisms.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory

set_option linter.style.haveILetI false

universe u v

/-- The pushforward of presheaves of modules along a functor of (opposite) sites preserves
monomorphisms. Monomorphisms of presheaves of modules are the pointwise injective maps, and
pushforward acts on underlying additive maps by a reindexing. -/
theorem presheafPushforward_preservesMonomorphisms {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D] {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}}
    {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R) :
    (PresheafOfModules.pushforward φ).PreservesMonomorphisms where
  preserves {M N} g hg := by
    refine (PresheafOfModules.mono_iff_surjective _).mpr fun U => ?_
    exact (PresheafOfModules.mono_iff_surjective g).mp hg (X := F.op.obj U)

/-- The pushforward of sheaves of modules along a continuous functor and a morphism of
sheaves of rings preserves monomorphisms. Since the forgetful functor to presheaves of
modules preserves and reflects monomorphisms, this follows from the presheaf statement. -/
theorem sheafPushforward_preservesMonomorphisms {C : Type u} [Category.{v} C]
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (SheafOfModules.pushforward ψ).PreservesMonomorphisms where
  preserves {M N} f hf := by
    haveI : Mono f := hf
    apply (SheafOfModules.forget S).mono_of_mono_map
    haveI : Mono ((SheafOfModules.forget R).map f) :=
      Functor.map_mono (SheafOfModules.forget R) f
    haveI := presheafPushforward_preservesMonomorphisms (F := F) ψ.hom
    exact Functor.map_mono (PresheafOfModules.pushforward ψ.hom)
      ((SheafOfModules.forget R).map f)

/-- Restriction of sheaves of modules along an open immersion preserves monomorphisms.
This is a special case of the general statement for pushforwards of sheaves of modules,
since `Scheme.Modules.restrictFunctor` is defined as a `SheafOfModules.pushforward`. -/
theorem restrict_preservesMonomorphisms {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).PreservesMonomorphisms := by
  apply sheafPushforward_preservesMonomorphisms

theorem pushforward_injective {X : AlgebraicGeometry.Scheme.{u}} (W : X.Opens)
    (I : SheafOfModules W.toScheme.ringCatSheaf) [CategoryTheory.Injective I] :
    CategoryTheory.Injective ((AlgebraicGeometry.Scheme.Modules.pushforward W.ι).obj I) := by
  haveI : (AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).PreservesMonomorphisms :=
    restrict_preservesMonomorphisms W.ι
  haveI : (AlgebraicGeometry.Scheme.Modules.pushforward W.ι).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction W.ι)
  exact Functor.injective_obj_of_injective _
    (show CategoryTheory.Injective I from ‹CategoryTheory.Injective I›)

end Work.DSF1.Sheaf
