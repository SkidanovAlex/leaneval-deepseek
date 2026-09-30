import Mathlib
import ChallengeDeps
import Submission.Work.Homology.All
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

abbrev simplex (n : ℕ) : TopCat := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))

def simplexBoundary (n : ℕ) : Set (simplex n) := {w | ∃ i : Fin (n + 1), w.weights i = 0}

abbrev boundarySpace (n : ℕ) : TopCat := TopCat.of (simplexBoundary n)

theorem isClosed_simplexBoundary (n : ℕ) : IsClosed (simplexBoundary n) := by
  have h : simplexBoundary n = ⋃ i : Fin (n + 1),
      (fun w : simplex n => w.weights i) ⁻¹' {0} := by
    ext w
    simp [simplexBoundary]
  rw [h]
  exact isClosed_iUnion_of_finite fun i => isClosed_eq (by fun_prop) continuous_const

/-- naturality of `TopCat.toSSetObjEquiv` in the space. -/
theorem toSSetObjEquiv_map_apply {X Y : TopCat} (g : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj X).obj n) (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    TopCat.toSSetObjEquiv Y n ((TopCat.toSSet.map g).app n x) z =
      g (TopCat.toSSetObjEquiv X n x z) := rfl

abbrev simplexId (n : ℕ) :
    (TopCat.toSSet.obj (simplex n)).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquiv (simplex n) (Opposite.op (SimplexCategory.mk n))).symm
    (ContinuousMap.id (simplex n))

@[simp]
theorem toSSetObjEquiv_simplexId (n : ℕ) :
    TopCat.toSSetObjEquiv (simplex n) (Opposite.op (SimplexCategory.mk n)) (simplexId n) =
      ContinuousMap.id (simplex n) :=
  Equiv.apply_symm_apply _ _

/-- the singular simplex of a continuous map out of `Δⁿ`. -/
abbrev simplexOf {X : TopCat} (n : ℕ) (f : C(simplex n, X)) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm f

@[simp]
theorem toSSetObjEquiv_simplexOf {X : TopCat} (n : ℕ) (f : C(simplex n, X)) :
    TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n)) (simplexOf n f) = f :=
  Equiv.apply_symm_apply _ _

abbrev simplexFaceCM (n : ℕ) (i : Fin (n + 2)) : C(simplex n, simplex (n + 1)) :=
  ⟨Convexity.StdSimplex.map i.succAbove, by fun_prop⟩

abbrev simplexFace (n : ℕ) (i : Fin (n + 2)) : simplex n ⟶ simplex (n + 1) :=
  TopCat.ofHom (simplexFaceCM n i)

theorem simplexFace_mem_boundary (n : ℕ) (i : Fin (n + 2)) (w : simplex n) :
    simplexFace n i w ∈ simplexBoundary (n + 1) := by
  refine ⟨i, ?_⟩
  show (Convexity.StdSimplex.map i.succAbove w).weights i = 0
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨j, hj⟩
  exact Fin.succAbove_ne i j hj

abbrev simplexFaceToBoundaryCM (n : ℕ) (i : Fin (n + 2)) : C(simplex n, boundarySpace (n + 1)) :=
  ⟨fun w => ⟨simplexFace n i w, simplexFace_mem_boundary n i w⟩, by fun_prop⟩

abbrev simplexFaceToBoundary (n : ℕ) (i : Fin (n + 2)) : simplex n ⟶ boundarySpace (n + 1) :=
  TopCat.ofHom (simplexFaceToBoundaryCM n i)

abbrev faceSimplex {X : TopCat} (n : ℕ) (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) :=
  (TopCat.toSSet.obj X).δ i σ

theorem simplexId_face_apply (n : ℕ) (i : Fin (n + 2))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))
        (faceSimplex n i (simplexId (n + 1))) z =
      TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSet.map (simplexFace n i)).app (Opposite.op (SimplexCategory.mk n))
          (simplexId n)) z := by
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_map_apply, toSSetObjEquiv_simplexId,
    toSSetObjEquiv_simplexId]
  rfl

theorem simplexId_face (n : ℕ) (i : Fin (n + 2)) :
    faceSimplex n i (simplexId (n + 1)) =
      (TopCat.toSSet.map (simplexFace n i)).app (Opposite.op (SimplexCategory.mk n))
        (simplexId n) := by
  apply (TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))).injective
  exact ContinuousMap.ext fun z => simplexId_face_apply n i z

abbrev simplexBoundaryFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (boundarySpace (n + 1))).obj (Opposite.op (SimplexCategory.mk n)) :=
  simplexOf n (simplexFaceToBoundaryCM n i)

theorem simplexBoundaryFaceSimplex_map_apply (n : ℕ) (i : Fin (n + 2))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSet.map (Work.Homology.incl (simplexBoundary (n + 1)))).app
          (Opposite.op (SimplexCategory.mk n)) (simplexBoundaryFaceSimplex n i)) z =
      TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))
        (faceSimplex n i (simplexId (n + 1))) z := by
  rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_simplexOf, simplexId_face_apply]
  rfl

theorem simplexBoundaryFaceSimplex_map (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.map (Work.Homology.incl (simplexBoundary (n + 1)))).app
        (Opposite.op (SimplexCategory.mk n)) (simplexBoundaryFaceSimplex n i) =
      faceSimplex n i (simplexId (n + 1)) := by
  apply (TopCat.toSSetObjEquiv (simplex (n + 1)) (Opposite.op (SimplexCategory.mk n))).injective
  exact ContinuousMap.ext fun z => simplexBoundaryFaceSimplex_map_apply n i z

/-! ## The chains of the identity simplex and of its faces -/

/-- The chain of a singular simplex, in the singular chains of the ambient space. -/
abbrev simpChain {X : TopCat} (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    Work.Homology.ZMod ⟶ (Work.Homology.singChain Work.Homology.ZMod X).X n :=
  SSet.ιChainComplex (TopCat.toSSet.obj X) σ

/-- The chain of the identity `n`-simplex, in `Cₙ(Δⁿ; ℤ)`. -/
abbrev simplexIdChain (n : ℕ) : Work.Homology.ZMod ⟶
    (Work.Homology.singChain Work.Homology.ZMod (simplex n)).X n :=
  simpChain n (simplexId n)

/-- The `i`-th face of `ιₙ₊₁`, as a chain of the boundary `∂Δⁿ⁺¹`. -/
abbrev simplexBoundaryFaceChain (n : ℕ) (i : Fin (n + 2)) : Work.Homology.ZMod ⟶
    (Work.Homology.singChain Work.Homology.ZMod (boundarySpace (n + 1))).X n :=
  simpChain n (simplexBoundaryFaceSimplex n i)

/-- The `i`-th face of `ιₙ₊₁`, as a chain of `Δⁿ⁺¹`. -/
abbrev simplexIdFaceChain (n : ℕ) (i : Fin (n + 2)) : Work.Homology.ZMod ⟶
    (Work.Homology.singChain Work.Homology.ZMod (simplex (n + 1))).X n :=
  simpChain n (faceSimplex n i (simplexId (n + 1)))

/-- **The boundary of the identity simplex**: `∂ιₙ₊₁ = ∑ᵢ (-1)ⁱ (i-th face)`. -/
theorem simplexIdChain_d (n : ℕ) :
    simplexIdChain (n + 1) ≫
        (Work.Homology.singChain Work.Homology.ZMod (simplex (n + 1))).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • simplexIdFaceChain n i :=
  SSet.ιChainComplex_d _ _ _

/-- **The `i`-th face of `ιₙ₊₁` lies in the boundary**: viewed in `Δⁿ⁺¹`, it is the image of the
corresponding chain of the boundary `∂Δⁿ⁺¹`. -/
theorem simplexIdFaceChain_eq_incl (n : ℕ) (i : Fin (n + 2)) :
    simplexBoundaryFaceChain n i ≫ (Work.Homology.inclChain Work.Homology.ZMod
        (simplex (n + 1)) (simplexBoundary (n + 1))).f n = simplexIdFaceChain n i := by
  show SSet.ιChainComplex (TopCat.toSSet.obj (boundarySpace (n + 1)))
      (simplexBoundaryFaceSimplex n i) ≫ (SSet.chainComplexMap
        (TopCat.toSSet.map (Work.Homology.incl (simplexBoundary (n + 1))))
        Work.Homology.ZMod).f n = _
  rw [SSet.ι_chainComplexMap_f, simplexBoundaryFaceSimplex_map]

/-- **The fundamental cycle of `∂Δⁿ⁺¹`**: the alternating sum of the codimension one faces of the
identity `(n+1)`-simplex, as a chain of the boundary subspace. -/
abbrev simplexBoundaryChain (n : ℕ) : Work.Homology.ZMod ⟶
    (Work.Homology.singChain Work.Homology.ZMod (boundarySpace (n + 1))).X n :=
  ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • simplexBoundaryFaceChain n i

/-- **The class of the identity simplex in the relative chains `Cₙ(Δⁿ, ∂Δⁿ)`.** -/
abbrev simplexRelChain (n : ℕ) : Work.Homology.ZMod ⟶
    (Work.Homology.relChain Work.Homology.ZMod (simplex n) (simplexBoundary n)).X n :=
  simplexIdChain n ≫
    (Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n)).f n

/-- The fundamental cycle of `∂Δⁿ⁺¹` maps to the boundary of the identity simplex. -/
theorem simplexBoundaryChain_incl (n : ℕ) :
    simplexBoundaryChain n ≫ (Work.Homology.inclChain Work.Homology.ZMod (simplex (n + 1))
        (simplexBoundary (n + 1))).f n =
      simplexIdChain (n + 1) ≫
        (Work.Homology.singChain Work.Homology.ZMod (simplex (n + 1))).d (n + 1) n := by
  rw [simplexIdChain_d, simplexBoundaryChain, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Preadditive.zsmul_comp, simplexIdFaceChain_eq_incl]

/-! ## The caps and the band of the simplex boundary

The boundary `∂Δⁿ⁺¹` of the standard `(n+1)`-simplex is covered by the two open sets
`northCap n = {w : 0 < w_v}` and `southCap n = {w : w_v < 1}` (where `v = Fin.last n` is the last
vertex): each is contractible, and their intersection is the **band**
`{w : 0 < w_v < 1}`, which deformation retracts onto the **equator** `∂F_v`, the boundary of the
face opposite `v`.  This is the simplex analogue of the two caps and the equatorial band of the
round sphere, and it is the geometric input of the Mayer–Vietoris computation of `H_*(∂Δⁿ⁺¹)`.
-/

/-- The "north cap" of `∂Δⁿ⁺¹`: the points whose barycentric coordinate at the last vertex is
positive.  It is the open star of that vertex, hence homeomorphic to an open disk. -/
def simplexNorthCap (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | 0 < (x : simplex (n + 1)).weights (Fin.last (n + 1))}

/-- The "south cap" of `∂Δⁿ⁺¹`: the points whose barycentric coordinate at the last vertex is
`< 1`, i.e. all points of the boundary except that vertex. -/
def simplexSouthCap (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | (x : simplex (n + 1)).weights (Fin.last (n + 1)) < 1}

/-- The **equator** of `∂Δⁿ⁺¹`: the boundary of the face opposite the last vertex. -/
def simplexEquator (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | (x : simplex (n + 1)).weights (Fin.last (n + 1)) = 0 ∧
    ∃ i : Fin (n + 1), (x : simplex (n + 1)).weights (Fin.castSucc i) = 0}

/-- The **band** of `∂Δⁿ⁺¹`: the points whose barycentric coordinate at the last vertex lies
strictly between `0` and `1`; it is the intersection of the two caps. -/
def simplexBand (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | 0 < (x : simplex (n + 1)).weights (Fin.last (n + 1)) ∧
    (x : simplex (n + 1)).weights (Fin.last (n + 1)) < 1}

/-- The band is the intersection of the two caps. -/
theorem simplexBand_eq_inter (n : ℕ) :
    simplexBand n = simplexNorthCap n ∩ simplexSouthCap n := rfl

end

end Work.HomologyExtra
