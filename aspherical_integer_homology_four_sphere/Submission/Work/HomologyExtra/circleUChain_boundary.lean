import Mathlib
import Submission.Work.HomologyExtra.SimplexCircleCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The boundary of the `U`-part of the fundamental cycle of `∂Δ²`

Let `X := ∂Δ²`, with the two-element open cover `circleU = {w 0 < 1/2}`,
`circleV = {w 1 < 1/2} ∪ {w 2 < 1/2}` of `Submission/Work/HomologyExtra/SimplexCircleCover.lean`.

The `U`-part of the fundamental cycle is the chain `circleUChain` of the edge `F₀ = [v₁,v₂]` of
`∂Δ²`, regarded as a chain of the subspace `circleU` (the edge `F₀ = {w 0 = 0}` lies in `circleU`).

This file computes its boundary.  Since `F₀` is the first face of `∂Δ²`, which sends the vertices
`0`, `1` of `Δ¹` to the vertices `v₁`, `v₂` of `∂Δ²`, the boundary of `circleUChain` is
`[v₂] - [v₁]`, and this is exactly the image under the inclusion `circleU ∩ circleV ↪ circleU` of
the `0`-chain `circleIntersectionChain = [v₂] - [v₁]` of the intersection:

`∂ x_U = (i_{U∩V,U})_* x₁`.

This is the first of the two chain-level inputs of the Mayer–Vietoris computation of the
fundamental class of `∂Δ²` (see `Work.HomologyExtra.circleMV_computation`).

## Main results

* `circleUMap` — the continuous map `Δ¹ → circleU` underlying `circleUChain`;
* `circleUChain_eq_ιChainComplex` — `circleUChain` is the chain of that `1`-simplex;
* `simplexPoint_circleUMap_single_one`, `simplexPoint_circleUMap_single_zero` — the two vertices
  of `Δ¹` map to the points `v₂`, `v₁` of `circleU`;
* `circleUChain_boundary` — `∂ x_U = (i_{U∩V,U})_* x₁`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-- **The continuous map `Δ¹ ⟶ circleU` underlying `circleUChain`**: the edge
`F₀ = [v₁,v₂] = {w 0 = 0}` of `∂Δ²`, whose image lies in `circleU`.

It is characterised by the fact that it is the composite of the first face
`simplexFaceToBoundary 1 0 : Δ¹ ⟶ ∂Δ²` with the inclusion `circleU ↪ ∂Δ²`. -/
def circleUMap : C(simplex 1, TopCat.of ↥circleU) :=
  ⟨fun z => ⟨(TopCat.toSSetObjEquiv (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
      (simplexBoundaryFaceSimplex 1 0)) z, circleFace0_mem_circleU z⟩,
   Continuous.subtype_mk
     ((TopCat.toSSetObjEquiv (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
       (simplexBoundaryFaceSimplex 1 0))).continuous circleFace0_mem_circleU⟩

/-- `circleUChain` is the chain of the singular `1`-simplex `circleUMap` of the subspace
`circleU`. -/
theorem circleUChain_eq_ιChainComplex :
    circleUChain = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleU))
      (simplexOf 1 circleUMap) := rfl

/-- The second vertex (`single 1`) of `Δ¹` is mapped by `circleUMap` to the vertex `v₂` of `∂Δ²`,
regarded as a point of `circleU` (via `circleU ∩ circleV`). -/
theorem circleUMap_single_one :
    circleUMap (Convexity.StdSimplex.single 1)
      = (Work.Cohomology.inclUVU circleU circleV) circleInterV2 := by
  apply Subtype.ext
  simp [circleUMap, Convexity.StdSimplex.map_single,
    Work.Cohomology.inclUVU, circleInterV2, circleVertex, simplexFaceToBoundaryCM, simplexFaceCM,
    simplexFace]

/-- The first vertex (`single 0`) of `Δ¹` is mapped by `circleUMap` to the vertex `v₁` of `∂Δ²`,
regarded as a point of `circleU` (via `circleU ∩ circleV`). -/
theorem circleUMap_single_zero :
    circleUMap (Convexity.StdSimplex.single 0)
      = (Work.Cohomology.inclUVU circleU circleV) circleInterV1 := by
  apply Subtype.ext
  simp [circleUMap, Convexity.StdSimplex.map_single,
    Work.Cohomology.inclUVU, circleInterV1, circleVertex, simplexFaceToBoundaryCM, simplexFaceCM,
    simplexFace]

/-- The `0`-simplex of `circleU` at the second vertex of `Δ¹` is the image, under the inclusion
`circleU ∩ circleV ↪ circleU`, of the `0`-simplex at `v₂`. -/
theorem simplexPoint_circleUMap_single_one :
    simplexPoint (X := TopCat.of ↥circleU) (circleUMap (Convexity.StdSimplex.single 1))
      = (TopCat.toSSet.map (Work.Cohomology.inclUVU circleU circleV)).app
          (Opposite.op (SimplexCategory.mk 0))
          (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV2) := by
  apply TopCat.toSSetObj₀Equiv.injective
  rw [toSSetObj₀Equiv_simplexPoint]
  rw [show TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map
        (Work.Cohomology.inclUVU circleU circleV)).app (Opposite.op (SimplexCategory.mk 0))
          (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV2))
      = (Work.Cohomology.inclUVU circleU circleV) circleInterV2 from rfl]
  exact circleUMap_single_one

/-- The `0`-simplex of `circleU` at the first vertex of `Δ¹` is the image, under the inclusion
`circleU ∩ circleV ↪ circleU`, of the `0`-simplex at `v₁`. -/
theorem simplexPoint_circleUMap_single_zero :
    simplexPoint (X := TopCat.of ↥circleU) (circleUMap (Convexity.StdSimplex.single 0))
      = (TopCat.toSSet.map (Work.Cohomology.inclUVU circleU circleV)).app
          (Opposite.op (SimplexCategory.mk 0))
          (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV1) := by
  apply TopCat.toSSetObj₀Equiv.injective
  rw [toSSetObj₀Equiv_simplexPoint]
  rw [show TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map
        (Work.Cohomology.inclUVU circleU circleV)).app (Opposite.op (SimplexCategory.mk 0))
          (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV1))
      = (Work.Cohomology.inclUVU circleU circleV) circleInterV1 from rfl]
  exact circleUMap_single_zero

/-- **The boundary of the `U`-part of the fundamental cycle of `∂Δ²`**:
`∂ x_U = (i_{U∩V,U})_* x₁`. -/
theorem circleUChain_boundary :
    CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleUChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleU)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVU Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0) := by
  rw [circleUChain_eq_ιChainComplex]
  change SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleU)) (simplexOf 1 circleUMap) ≫
      ((TopCat.toSSet.obj (TopCat.of ↥circleU)).chainComplex Homology.ZMod).d 1 0
    = circleIntersectionChain ≫ (SSet.chainComplexMap
        (TopCat.toSSet.map (Work.Cohomology.inclUVU circleU circleV)) (ModuleCat.of ℤ ℤ)).f 0
  rw [gen_simplexOf_one_boundary_aux circleUMap]
  rw [circleIntersectionChain, Preadditive.sub_comp,
    SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f,
    simplexPoint_circleUMap_single_one, simplexPoint_circleUMap_single_zero]

end

end Work.HomologyExtra
