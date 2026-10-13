import Mathlib

/-!
# Restriction of sheaves of modules along an open immersion preserves homology

For a morphism of schemes `f : X ⟶ Y` which is an open immersion, the restriction functor
`Scheme.Modules.restrictFunctor f : Y.Modules ⥤ X.Modules` is exact, i.e. it preserves
homology of complexes (equivalently, it preserves kernels and cokernels).

The mathematical content is the following.

* `restrictFunctor f` is by definition a `SheafOfModules.pushforward` along the open map
  `f.opensFunctor` of the sites of open subsets; on underlying presheaves of modules it is
  given by `M ↦ M.presheaf ⋙ f.opensFunctor.op`, which is pointwise the identity map.
  Hence it preserves monomorphisms: monomorphisms of (pre)sheaves of modules are exactly the
  pointwise injective morphisms, and the pushforward acts by a reindexing.
* `restrictFunctor f` is left adjoint to `Scheme.Modules.pushforward f`
  (`Scheme.Modules.restrictAdjunction`), hence it preserves all colimits, in particular
  cokernels.

A functor between abelian categories which preserves zero morphisms, monomorphisms and
cokernels preserves homology (`Functor.preservesHomology_of_preservesMonos_and_cokernels`),
which gives the result.

## Main results

* `Work.DSEQ0.presheafPushforward_preservesMonomorphisms`
* `Work.DSEQ0.sheafPushforward_preservesMonomorphisms`
* `Work.DSEQ0.restrictFunctor_preservesMonomorphisms`
* `Work.DSEQ0.restrictFunctor_preservesHomology`
-/

namespace Work.DSEQ0

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
theorem restrictFunctor_preservesMonomorphisms {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).PreservesMonomorphisms := by
  apply sheafPushforward_preservesMonomorphisms

/-- The restriction of sheaves of modules along an open immersion preserves homology: it is
an exact functor. Indeed it preserves monomorphisms (see
`restrictFunctor_preservesMonomorphisms`) and, being a left adjoint
(`Scheme.Modules.restrictAdjunction`), it preserves cokernels. -/
theorem restrictFunctor_preservesHomology {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).PreservesHomology := by
  haveI : (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).PreservesMonomorphisms :=
    restrictFunctor_preservesMonomorphisms f
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

end Work.DSEQ0
