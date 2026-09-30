import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk.Finiteness

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
/-- **The group chunk `G D` is locally of finite type over `Spec K`.**

`G D = GSch D` is glued from the charts `V ⊆ Sym^g C`.  `LocallyOfFiniteType` is Zariski-local
at the source, and the chart inclusions `ι i : V ⟶ glued` form an open cover of the glued
scheme.  On the chart, the structure morphism of `G D` is (by `gluedHom_π`) the structure
morphism `V ⟶ Spec K` of the open subscheme `V` of `Sym^g C`, which is locally of finite type
as an open immersion composed with the locally finite type `Sym^g C ⟶ Spec K`. -/
theorem loft_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    LocallyOfFiniteType (Work.GroupChunk.GSch D).hom := by
  have hloc : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI := hloc
  show LocallyOfFiniteType (Work.GroupChunk.gluedHom D)
  -- The open cover of the glued scheme by the charts.
  let Ucov : (Work.GroupChunk.glueScheme D).glued.OpenCover :=
    { I₀ := D.Idx
      X := fun i => (Work.GroupChunk.glueScheme D).U i
      f := fun i => (Work.GroupChunk.glueScheme D).ι i
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => (Work.GroupChunk.glueScheme D).ι_jointly_surjective x,
          fun i => Scheme.GlueData.ι_isOpenImmersion (Work.GroupChunk.glueScheme D) i⟩ }
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) Ucov).mpr
    (fun i => ?_)
  show LocallyOfFiniteType ((Work.GroupChunk.glueScheme D).ι i ≫ Work.GroupChunk.gluedHom D)
  rw [Work.GroupChunk.gluedHom_π]
  -- On the chart, the structure morphism is that of the open subscheme `V ⊆ Sym^g C`.
  show LocallyOfFiniteType (D.V.ι ≫ (D.Sym D.g).hom)
  exact locallyOfFiniteType_comp D.V.ι (D.Sym D.g).hom

end Work.GroupChunk.Finiteness
