import Mathlib
import Submission.Work.HomologyExtra.SimplexCircleCover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The boundary of the `V`-part of the fundamental cycle of `∂Δ²`

`Work.HomologyExtra.circleVChain` is the chain `x_V = F₁ - F₂` of `circleV` (the two edges
`F₁ = [v₀,v₂]`, `F₂ = [v₀,v₁]` of `∂Δ²`, lifted to the open subset `circleV`), and
`Work.HomologyExtra.circleIntersectionChain` is the `0`-chain `x₁ = [v₂] - [v₁]` of
`circleU ∩ circleV`.  This file proves

`∂ x_V = (inclUVV)_* x₁`,

the `V`-half of the input to the Mayer–Vietoris computation of the fundamental class of `∂Δ²`
(the `U`-half is `circleUChain_boundary`).

The proof is the explicit boundary computation in the *ambient* space `∂Δ²`, followed by
cancellation against the monomorphism of singular chain complexes induced by the open inclusion
`circleV ⊆ ∂Δ²`:

* `boundary_liftSimplex_one` computes the boundary of the chain of a lifted `1`-simplex: it is the
  difference of the `0`-simplices at the images of the two vertices of `Δ¹`
  (this is `gen_simplexOf_one_boundary` for the continuous map defining the lift);
* `vertex_*` and `liftPoint_*` identify those two vertices as the points `v₀`, `v₁`, `v₂` of
  `circleV`;
* `toSSet_map_simplexPoint` and `point_inclUVV_*` compute the right hand side, which is the image
  under `(inclUVV)_*` of the `0`-chain `[v₂] - [v₁]` of `circleU ∩ circleV`.

Both sides are thus the same difference of `0`-simplices.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

namespace CircleVChainBoundary

/-! ## The vertices `v₀`, `v₁`, `v₂` as points of `circleV` -/

/-- The point `v₀` of `∂Δ²`, regarded as a point of `circleV`. -/
def point0 : ↥circleV := ⟨circleVertex 0, circleVertex_zero_mem_circleV⟩

/-- The point `v₁` of `∂Δ²`, regarded as a point of `circleV`. -/
def point1 : ↥circleV := ⟨circleVertex 1, circleVertex_one_mem_circleV⟩

/-- The point `v₂` of `∂Δ²`, regarded as a point of `circleV`. -/
def point2 : ↥circleV := ⟨circleVertex 2, circleVertex_two_mem_circleV⟩

/-- **The first vertex of the edge `F₁`** (the face `{w 1 = 0}` of `∂Δ²`) is `v₂`. -/
theorem face_one_single_one :
    simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (1 : Fin 2)) = circleVertex 2 := by
  apply Subtype.ext
  show (Convexity.StdSimplex.map (1 : Fin 3).succAbove
      (Convexity.StdSimplex.single (1 : Fin 2)) : Convexity.StdSimplex ℝ (Fin 3))
    = Convexity.StdSimplex.single (2 : Fin 3)
  rw [Convexity.StdSimplex.map_single]
  congr 1

/-- **The zeroth vertex of the edge `F₁`** is `v₀`. -/
theorem face_one_single_zero :
    simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (0 : Fin 2)) = circleVertex 0 := by
  apply Subtype.ext
  show (Convexity.StdSimplex.map (1 : Fin 3).succAbove
      (Convexity.StdSimplex.single (0 : Fin 2)) : Convexity.StdSimplex ℝ (Fin 3))
    = Convexity.StdSimplex.single (0 : Fin 3)
  rw [Convexity.StdSimplex.map_single]
  congr 1

/-- **The first vertex of the edge `F₂`** (the face `{w 2 = 0}` of `∂Δ²`) is `v₁`. -/
theorem face_two_single_one :
    simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (1 : Fin 2)) = circleVertex 1 := by
  apply Subtype.ext
  show (Convexity.StdSimplex.map (2 : Fin 3).succAbove
      (Convexity.StdSimplex.single (1 : Fin 2)) : Convexity.StdSimplex ℝ (Fin 3))
    = Convexity.StdSimplex.single (1 : Fin 3)
  rw [Convexity.StdSimplex.map_single]
  congr 1

/-- **The zeroth vertex of the edge `F₂`** is `v₀`. -/
theorem face_two_single_zero :
    simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (0 : Fin 2)) = circleVertex 0 := by
  apply Subtype.ext
  show (Convexity.StdSimplex.map (2 : Fin 3).succAbove
      (Convexity.StdSimplex.single (0 : Fin 2)) : Convexity.StdSimplex ℝ (Fin 3))
    = Convexity.StdSimplex.single (0 : Fin 3)
  rw [Convexity.StdSimplex.map_single]
  congr 1

/-! The same statements as equalities of points of `circleV`, in the form in which they occur
after the boundary computation (with the membership proof left as a metavariable, so that they can
be used as rewrite rules). -/

theorem facePoint_one_one
    (hp : simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (1 : Fin 2)) ∈ circleV) :
    (⟨simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (1 : Fin 2)), hp⟩ : ↥circleV)
      = point2 :=
  Subtype.ext face_one_single_one

theorem facePoint_one_zero
    (hp : simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (0 : Fin 2)) ∈ circleV) :
    (⟨simplexFaceToBoundaryCM 1 1 (Convexity.StdSimplex.single (0 : Fin 2)), hp⟩ : ↥circleV)
      = point0 :=
  Subtype.ext face_one_single_zero

theorem facePoint_two_one
    (hp : simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (1 : Fin 2)) ∈ circleV) :
    (⟨simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (1 : Fin 2)), hp⟩ : ↥circleV)
      = point1 :=
  Subtype.ext face_two_single_one

theorem facePoint_two_zero
    (hp : simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (0 : Fin 2)) ∈ circleV) :
    (⟨simplexFaceToBoundaryCM 1 2 (Convexity.StdSimplex.single (0 : Fin 2)), hp⟩ : ↥circleV)
      = point0 :=
  Subtype.ext face_two_single_zero

/-! ## Naturality of `simplexPoint` -/

/-- The `0`-simplex at a point is natural: pushing forward along a continuous map gives the
`0`-simplex at the image of the point. -/
theorem toSSet_map_simplexPoint {X Y : TopCat} (g : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map g).app (Opposite.op ⦋0⦌) (simplexPoint x) = simplexPoint (g x) := by
  apply simplexPoint_eq_of_apply_eq
  intro z
  rw [Work.HomologyExtra.toSSetObjEquiv_map_apply,
      Work.HomologyExtra.toSSetObjEquiv_simplexPoint]

/-- The inclusion `circleU ∩ circleV ↪ circleV` sends the point `v₂` to the point `v₂`. -/
theorem inclUVV_circleInterV2 :
    Work.Cohomology.inclUVV circleU circleV circleInterV2 = point2 := by
  apply Subtype.ext
  rw [Work.Cohomology.inclUVV]
  rfl

/-- The inclusion `circleU ∩ circleV ↪ circleV` sends the point `v₁` to the point `v₁`. -/
theorem inclUVV_circleInterV1 :
    Work.Cohomology.inclUVV circleU circleV circleInterV1 = point1 := by
  apply Subtype.ext
  rw [Work.Cohomology.inclUVV]
  rfl

/-! ## The boundary of the chain of a lifted `1`-simplex -/

/-- A `1`-simplex of `X` whose image lies in `A`, lifted to the subspace `A`, is the simplex of
the canonical continuous map `Δ¹ ⟶ A` it defines. -/
theorem liftSimplex_simplexOf_eq {X : TopCat} {A : Set X} (f : C(simplex 1, X))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) (simplexOf 1 f) z ∈ A) :
    Work.Homology.liftSimplex (simplexOf 1 f) h
      = simplexOf 1 (⟨fun z => ⟨f z, by simpa using h z⟩,
          Continuous.subtype_mk f.continuous (fun z => by simpa using h z)⟩ :
            C(simplex 1, TopCat.of A)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op ⦋1⦌)).injective
  rw [Work.Homology.toSSetObjEquiv_liftSimplex]
  conv_rhs => rw [Work.HomologyExtra.toSSetObjEquiv_simplexOf]
  apply ContinuousMap.ext
  intro z
  simp only [Work.HomologyExtra.toSSetObjEquiv_simplexOf]

/-- **The boundary of the chain of a lifted `1`-simplex** in a subspace: it is the difference of
the `0`-simplices at the images of the two vertices of `Δ¹` under the defining continuous map. -/
theorem boundary_liftSimplex_one {X : TopCat} {A : Set X} (f : C(simplex 1, X))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌) (simplexOf 1 f) z ∈ A) :
    (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (Work.Homology.liftSimplex (simplexOf 1 f) h)
        ≫ (Work.Homology.singChain Work.Homology.ZMod (TopCat.of A)).d 1 0
      = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
            (simplexPoint (X := TopCat.of A) ⟨f (Convexity.StdSimplex.single 1), by simpa using h _⟩)
          - (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
            (simplexPoint (X := TopCat.of A) ⟨f (Convexity.StdSimplex.single 0), by simpa using h _⟩) := by
  rw [liftSimplex_simplexOf_eq f h, gen_simplexOf_one_boundary]
  congr 1

end CircleVChainBoundary

open CircleVChainBoundary

/-- **The `V`-half of the Mayer–Vietoris input**: the boundary of the `V`-part `x_V = F₁ - F₂` of
the fundamental cycle of `∂Δ²` is the image of the `0`-chain `x₁ = [v₂] - [v₁]` of the intersection
`circleU ∩ circleV` under the chain map induced by the inclusion `circleU ∩ circleV ↪ circleV`. -/
theorem circleVChain_boundary :
    CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleVChain
        ((Work.Cohomology.singularChains ℤ (TopCat.of Work.HomologyExtra.circleV)).d 1 0)
      = CategoryTheory.CategoryStruct.comp Work.HomologyExtra.circleIntersectionChain
          ((SSet.chainComplexMap (TopCat.toSSet.map
              (Work.Cohomology.inclUVV Work.HomologyExtra.circleU Work.HomologyExtra.circleV))
              (ModuleCat.of ℤ ℤ)).f 0) := by
  rw [Work.HomologyExtra.circleVChain, Work.HomologyExtra.circleIntersectionChain]
  rw [Preadditive.sub_comp]
  rw [Preadditive.sub_comp]
  rw [boundary_liftSimplex_one (simplexFaceToBoundaryCM 1 1) circleFace1_mem_circleV,
      boundary_liftSimplex_one (simplexFaceToBoundaryCM 1 2) circleFace2_mem_circleV]
  rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  rw [toSSet_map_simplexPoint (Work.Cohomology.inclUVV circleU circleV) circleInterV2,
      toSSet_map_simplexPoint (Work.Cohomology.inclUVV circleU circleV) circleInterV1]
  rw [inclUVV_circleInterV2, inclUVV_circleInterV1]
  rw [facePoint_one_one, facePoint_one_zero, facePoint_two_one, facePoint_two_zero]
  abel

end

end Work.HomologyExtra
