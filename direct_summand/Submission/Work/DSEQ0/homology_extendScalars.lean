import Mathlib

/-!
# Homology commutes with extension of scalars along a flat algebra

Let `A → B` be a flat algebra (i.e. `B` is flat as an `A`-module), and let `C` be a cochain
complex of `A`-modules. Extension of scalars `- ⊗[A] B : ModuleCat A ⥤ ModuleCat B` is right
exact since it is a left adjoint (its right adjoint being restriction of scalars), and it is
left exact precisely because `B` is flat over `A`. Hence it is an exact functor, and any exact
functor preserves homology: there is a canonical isomorphism
`Hⁱ(C ⊗[A] B) ≅ Hⁱ(C) ⊗[A] B`.

The formal content is a specialisation of the following general principle: a functor
`F : C₁ ⥤ C₂` between categories with homology which preserves kernels and cokernels
(`F.PreservesHomology`) induces an isomorphism
`((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i)`.

## Main results

* `HomologicalComplex.mapHomologyIso`: homology commutes with a functor preserving homology.
* `Work.DSEQ0.extendScalars_preservesHomology`: extension of scalars along a flat algebra
  preserves homology.
* `Work.DSEQ0.homology_extendScalars`: `Hⁱ(C ⊗[A] B) ≅ Hⁱ(C) ⊗[A] B` for `B` flat over `A`.
-/

namespace Work.DSEQ0

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

universe u₁ u₂ v₁ v₂ u

namespace HomologicalComplex

/-- For a functor `F : C₁ ⥤ C₂` between categories with homology which preserves kernels and
cokernels (`F.PreservesHomology`), the homology of the complex `(F.mapHomologicalComplex c).obj K`
is canonically isomorphic to `F.obj (K.homology i)`.

Indeed, `K.homology i` is by definition the homology of the short complex `K.sc i`, and a functor
preserving homology preserves the left homology data of any short complex. -/
noncomputable def mapHomologyIso {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
    (F : C₁ ⥤ C₂) [F.PreservesZeroMorphisms] [CategoryWithHomology C₁] [CategoryWithHomology C₂]
    [F.PreservesHomology] {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C₁ c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  ShortComplex.mapHomologyIso (K.sc i) F

end HomologicalComplex

/-- Extension of scalars along a flat algebra preserves homology.

`ModuleCat.extendScalars (algebraMap A B)` is left adjoint to restriction of scalars, hence
preserves finite colimits; it preserves finite limits by flatness of `B` over `A`
(`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`). A functor preserving finite limits and
finite colimits preserves homology. -/
theorem extendScalars_preservesHomology (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).PreservesHomology := by
  have hf : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat A B)
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact Functor.preservesHomologyOfExact _

/-- **Homology commutes with extension of scalars along a flat algebra.**

If `B` is flat as an `A`-module and `C` is a cochain complex of `A`-modules, then the `i`-th
homology of `C ⊗[A] B` is canonically isomorphic to `Hⁱ(C) ⊗[A] B`. -/
theorem homology_extendScalars (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Module.Flat A B] (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Nonempty (HomologicalComplex.homology
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) i ≅
      (ModuleCat.extendScalars (algebraMap A B)).obj (C.homology i)) := by
  haveI := extendScalars_preservesHomology A B
  exact ⟨HomologicalComplex.mapHomologyIso (ModuleCat.extendScalars (algebraMap A B)) C i⟩

end Work.DSEQ0
