import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.GroupChunk.GeomProps

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry
open Work.GCBasics

universe u

/-! ## Locality of `GeometricallyReduced` in the source

Two general facts, neither of which is in Mathlib:

* `gR_openImmersion`: geometrically reduced morphisms stay geometrically reduced when the
  source is restricted along an open immersion;
* `gR_openCover`: geometric reducedness is Zariski-local in the source.

They are proved by pulling back an arbitrary pullback square of the given morphism along the
open immersion / the members of the open cover and pasting the resulting squares. -/

/-- Geometrically reduced is stable under restricting the source along an open immersion. -/
theorem gR_openImmersion {X X' S : Scheme.{u}} (i : X' ⟶ X) [IsOpenImmersion i]
    {f : X ⟶ S} (hf : GeometricallyReduced f) : GeometricallyReduced (i ≫ f) := by
  refine ⟨fun K _ y Z fst snd hpb => ?_⟩
  haveI : HasPullback (i ≫ f) y := hpb.hasPullback
  have hW : IsReduced (pullback f y) :=
    hf.geometrically_isReduced (K := K) y (pullback.fst f y) (pullback.snd f y)
      (IsPullback.of_hasPullback f y)
  haveI : IsReduced (pullback f y) := hW
  have hWi : IsReduced (pullback i (pullback.fst f y)) :=
    isReduced_of_isOpenImmersion (pullback.snd i (pullback.fst f y))
  have hpasted : IsPullback (pullback.fst i (pullback.fst f y))
      (pullback.snd i (pullback.fst f y) ≫ pullback.snd f y) (i ≫ f) y :=
    IsPullback.paste_vert (IsPullback.of_hasPullback i (pullback.fst f y))
      (IsPullback.of_hasPullback f y)
  exact ObjectProperty.prop_of_iso (fun X : Scheme => IsReduced X)
    (hpb.isoPullback.trans hpasted.isoPullback.symm).symm hWi

/-- Geometrically reduced is Zariski-local in the source: a morphism is geometrically
reduced as soon as its restrictions to the members of an open cover of the source are. -/
theorem gR_openCover {X S : Scheme.{u}} {f : X ⟶ S} (𝒰 : X.OpenCover)
    (h : ∀ i, GeometricallyReduced (𝒰.f i ≫ f)) : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd hpb => ?_⟩
  have key : ∀ i, IsReduced (pullback (𝒰.f i) fst) := by
    intro i
    have hpasted : IsPullback (pullback.fst (𝒰.f i) fst)
        (pullback.snd (𝒰.f i) fst ≫ snd) (𝒰.f i ≫ f) y :=
      IsPullback.paste_vert (IsPullback.of_hasPullback (𝒰.f i) fst) hpb
    exact (h i).geometrically_isReduced (K := K) y _ _ hpasted
  have hcov : ∀ z : Z, ∃ i w, pullback.snd (𝒰.f i) fst w = z := by
    intro z
    have hz : fst z ∈ (𝒰.f (𝒰.idx (fst z))).opensRange :=
      Scheme.Hom.mem_opensRange.mpr (𝒰.covers (fst z))
    have hz2 : z ∈ Set.range (pullback.snd (𝒰.f (𝒰.idx (fst z))) fst) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hz
    obtain ⟨w, hw⟩ := hz2
    exact ⟨𝒰.idx (fst z), w, hw⟩
  let 𝒱 : Z.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
    (fun i => pullback (𝒰.f i) fst) (fun i => pullback.snd (𝒰.f i) fst) hcov
  haveI : ∀ i, IsReduced (𝒱.X i) := key
  exact IsReduced.of_openCover Z 𝒱

open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem geometricallyReduced_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    GeometricallyReduced (Work.GroupChunk.GSch D).hom := by
  -- The chart `V ⊆ Sym^g C` is geometrically reduced: `Sym^g C` is geometrically integral,
  -- hence geometrically reduced, and `V` is an open subscheme.
  haveI : GeometricallyIntegral ((D.symGeom D.g).S).hom := D.geomIntegral_Sym D.g
  have hred : GeometricallyReduced ((D.symGeom D.g).S).hom := inferInstance
  have hV : GeometricallyReduced (Opens.toOver D.V).hom := gR_openImmersion D.V.ι hred
  -- The glued group chunk is covered by its charts, over each of which it is geometrically
  -- reduced by the previous step.
  let 𝒰 : (GSch D).left.OpenCover := Scheme.Cover.mkOfCovers D.Idx
    (fun i => Vsch D) (fun i => (glueScheme D).ι i)
    (fun x => Scheme.GlueData.ι_jointly_surjective (glueScheme D) x)
    (fun i => isOpenImmersion_ι_glue D i)
  refine gR_openCover 𝒰 (fun i => ?_)
  have hw : (𝒰.f i ≫ (GSch D).hom) = (Opens.toOver D.V).hom :=
    Over.w (chartH D i)
  rw [hw]
  exact hV

end Work.GroupChunk.GeomProps
