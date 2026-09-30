import Mathlib
import Submission.Work.GCBasics.All
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.Separated

universe u
open CategoryTheory in
/-- Every `R`-valued point of the glued group chunk `GSch D`, for `R` a *local* `K`-algebra,
factors through one of the chart maps `chartH D i`.

The point of the proof is that the closed point of `Spec R` is a specialisation of *every*
point of `Spec R` (`IsLocalRing.specializes_closedPoint`), and the range of an open
immersion is closed under specialisation.  Hence if the closed point lands in the (open)
range of the `i`-th chart -- which happens for some `i` because the charts cover the glued
scheme (`Scheme.GlueData.ι_jointly_surjective`) -- then the whole image of `p` lies in that
range, and `p` lifts along the open immersion `(chartH D i).left`
(`IsOpenImmersion.lift`). -/
theorem exists_chart_factor {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) {R : Type u} [CommRing R] [IsLocalRing R] [Algebra K R]
    (p : Work.GCBasics.RPt (Work.GroupChunk.GSch D) R) :
    ∃ (i : D.Idx) (a : Work.GCBasics.RPt (Work.GCBasics.Opens.toOver D.V) R),
      a ≫ Work.GroupChunk.chartH D i = p := by
  -- the closed point of `Spec R` lies in the range of one of the charts
  obtain ⟨i, y, hy⟩ := (Work.GroupChunk.glueScheme D).ι_jointly_surjective
    (p.left (IsLocalRing.closedPoint R))
  -- the `i`-th chart, as an open immersion of plain schemes
  let iota : (Work.GCBasics.Opens.toOver D.V).left ⟶ (Work.GroupChunk.GSch D).left :=
    (Work.GroupChunk.chartH D i).left
  have hiso : AlgebraicGeometry.IsOpenImmersion iota :=
    AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion (Work.GroupChunk.glueScheme D) i
  have hy' : iota y = p.left (IsLocalRing.closedPoint R) := hy
  have hrange : IsOpen (Set.range iota) :=
    @AlgebraicGeometry.IsOpenImmersion.isOpen_range _ _ iota hiso
  -- every point of `Spec R` specialises to the closed point, so the whole image of `p`
  -- lies in the (open) range of the chart
  have hle : Set.range p.left ⊆ Set.range iota := by
    rintro _ ⟨s, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint s).map p.left.continuous).mem_open hrange ⟨y, hy'⟩
  -- lift `p` along the open immersion
  let q0 : (Work.GCBasics.specOf K R).left ⟶ (Work.GCBasics.Opens.toOver D.V).left :=
    @AlgebraicGeometry.IsOpenImmersion.lift _ _ _ iota p.left hiso hle
  have hlift : q0 ≫ iota = p.left :=
    @AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _ iota p.left hiso hle
  -- the lift is a morphism of `K`-schemes, because the chart map is
  have hfac : iota ≫ (Work.GroupChunk.GSch D).hom
      = (Work.GCBasics.Opens.toOver D.V).hom :=
    Over.Hom.w (Work.GroupChunk.chartH D i)
  refine ⟨i, Over.homMk q0 ?_, ?_⟩
  · rw [← hfac, ← Category.assoc, hlift]
    exact p.w
  · apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact hlift

end Work.GroupChunk.Separated
