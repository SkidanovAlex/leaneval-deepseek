import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.simplexGenMap_pairdelta
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.SmallSES

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A two-element open cover of `∂Δ²` adapted to the fundamental cycle

This file sets up the elementary geometry used in the proof that the fundamental class of `∂Δ²`
generates `H₁(∂Δ²; ℤ)`.

Let `X := ∂Δ²` be the boundary of the standard `2`-simplex, with barycentric coordinates
`w 0, w 1, w 2` (summing to `1`, at least one of them `0`), and let `v i` be its `i`-th vertex.
The **fundamental cycle** is the `1`-chain `z₁ = F₀ - F₁ + F₂`, where `F i` is the `i`-th edge of
`∂Δ²`; the edges are
`F₀ = {w 0 = 0} = [v₁,v₂]`, `F₁ = {w 1 = 0} = [v₀,v₂]`, `F₂ = {w 2 = 0} = [v₀,v₁]`.

We use the open cover of `X` by

* `circleU = {w 0 < 1/2}`,
* `circleV = {w 1 < 1/2} ∪ {w 2 < 1/2}`,

which is chosen so that `F₀ ⊆ circleU` and `F₁ ∪ F₂ ⊆ circleV`.  Hence the fundamental cycle is
*small* for the cover without any subdivision:
`z₁ = F₀ - (F₁ - F₂)` with `F₀` a chain of `circleU` and `F₁ - F₂` a chain of `circleV`.  The
intersection `circleU ∩ circleV` is the disjoint union of the two open arcs

* `P₁ = {w 0 < 1/2, w 2 < 1/2} ∋ v₁` and `P₂ = {w 0 < 1/2, w 1 < 1/2} ∋ v₂`,

so that `v₁` and `v₂` lie in *different* components of the intersection.  This is what makes the
Mayer–Vietoris connecting map of the class of `z₁` non-trivial: its value is the class of the
`0`-chain `[v₂] - [v₁]` in `H₀(circleU ∩ circleV) ≅ ℤ ⊕ ℤ`, a generator of the kernel of the map
of the sequence.

## Main definitions

* `simplexPoint x` — the singular `0`-simplex at the point `x`;
* `gen_simplexOf_one_boundary` — the boundary of the chain of a `1`-simplex in terms of its two
  vertices;
* `circleU`, `circleV`, `circleVertex`;
* `circleUChain`, `circleVChain`, `circleSmallChain`, `circleIntersectionChain` — the chains
  `x_U`, `x_V`, `x₃`, `x₁` of the argument;
* `circlePsi` — the functional `H₀(circleU ∩ circleV) ⟶ ℤ` detecting the component of `v₂`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-! ## Singular `0`-simplices and the boundary of a `1`-simplex -/

/-- **The singular `0`-simplex at a point** of a topological space. -/
def simplexPoint {X : TopCat} (x : X) : (TopCat.toSSet.obj X) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))).symm (ContinuousMap.const _ x)

theorem toSSetObjEquiv_simplexPoint {X : TopCat} (x : X)
    (z : Convexity.StdSimplex ℝ (Fin (0 + 1))) :
    TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0)) (simplexPoint x) z = x := by
  simp [simplexPoint]

@[simp]
theorem toSSetObj₀Equiv_simplexPoint {X : TopCat} (x : X) :
    TopCat.toSSetObj₀Equiv (simplexPoint x) = x := rfl

/-- A `0`-simplex all of whose values are the point `x` *is* the `0`-simplex at `x`. -/
theorem simplexPoint_eq_of_apply_eq {X : TopCat} {x : X} {σ : (TopCat.toSSet.obj X) _⦋0⦌}
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0)) σ z = x) :
    σ = simplexPoint x := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))).injective
  exact ContinuousMap.ext fun z => by rw [toSSetObjEquiv_simplexPoint, h z]

/-- The `i`-th face of the `1`-simplex of a map `f : Δ¹ → X` is the `0`-simplex at the image of
the corresponding vertex of `Δ¹`. -/
theorem delta_simplexOf_one {X : TopCat} (f : C(simplex 1, X)) (i : Fin 2) :
    (TopCat.toSSet.obj X).δ i (simplexOf 1 f)
      = simplexPoint (f (Convexity.StdSimplex.single (i.succAbove 0))) := by
  apply simplexPoint_eq_of_apply_eq
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplexOf]
  congr 1
  have hz : z = (Convexity.StdSimplex.single 0 : Convexity.StdSimplex ℝ (Fin 1)) :=
    Subsingleton.elim _ _
  rw [hz, Convexity.StdSimplex.map_single]

/-- **The boundary of the chain of a `1`-simplex** `f : Δ¹ → X` is the difference of the
`0`-simplices at the images of the two vertices of `Δ¹`. -/
theorem gen_simplexOf_one_boundary_aux {X : TopCat} (f : C(simplex 1, X)) :
    SSet.ιChainComplex (TopCat.toSSet.obj X) (simplexOf 1 f) ≫
        ((TopCat.toSSet.obj X).chainComplex Work.Homology.ZMod).d 1 0
      = SSet.ιChainComplex (TopCat.toSSet.obj X) (simplexPoint (f (Convexity.StdSimplex.single 1)))
        - SSet.ιChainComplex (TopCat.toSSet.obj X)
            (simplexPoint (f (Convexity.StdSimplex.single 0))) := by
  rw [show SSet.ιChainComplex (TopCat.toSSet.obj X) (simplexOf 1 f) ≫
      ((TopCat.toSSet.obj X).chainComplex Work.Homology.ZMod).d 1 0
      = ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • SSet.ιChainComplex (TopCat.toSSet.obj X)
          ((TopCat.toSSet.obj X).δ i (simplexOf 1 f)) from
    SSet.ιChainComplex_d (TopCat.toSSet.obj X) Work.Homology.ZMod (simplexOf 1 f)]
  rw [Fin.sum_univ_two, delta_simplexOf_one f 0, delta_simplexOf_one f 1]
  norm_num [Fin.succAbove]
  rw [sub_eq_add_neg]

/-- The same statement with the chain complexes written as `Work.Homology.singChain`. -/
theorem gen_simplexOf_one_boundary {X : TopCat} (f : C(simplex 1, X)) :
    SSet.ιChainComplex (TopCat.toSSet.obj X) (simplexOf 1 f) ≫
        (Work.Homology.singChain Work.Homology.ZMod X).d 1 0
      = SSet.ιChainComplex (TopCat.toSSet.obj X) (simplexPoint (f (Convexity.StdSimplex.single 1)))
        - SSet.ιChainComplex (TopCat.toSSet.obj X)
            (simplexPoint (f (Convexity.StdSimplex.single 0))) :=
  gen_simplexOf_one_boundary_aux f


/-! ## The barycentric coordinates of `∂Δ²` -/

/-- The `i`-th barycentric coordinate of a point of `∂Δ²`. -/
def circleWeight (x : boundarySpace 2) (i : Fin 3) : ℝ := (x : simplex 2).weights i

theorem circleWeight_nonneg (x : boundarySpace 2) (i : Fin 3) : 0 ≤ circleWeight x i :=
  Convexity.StdSimplex.weights_nonneg (w := (x : simplex 2)) i

theorem circleWeight_sum (x : boundarySpace 2) :
    circleWeight x 0 + circleWeight x 1 + circleWeight x 2 = 1 := by
  have h := (x : simplex 2).total_of_fintype
  rw [Fin.sum_univ_three] at h
  simpa [circleWeight] using h

/-- A point of `∂Δ²` has a vanishing barycentric coordinate. -/
theorem circleWeight_exists_zero (x : boundarySpace 2) : ∃ i : Fin 3, circleWeight x i = 0 := x.2

/-! ## The two open sets of the cover -/

/-- The open set of the cover containing the edge `F₀ = {w 0 = 0}`. -/
def circleU : Set (boundarySpace 2) := {x | circleWeight x 0 < 1/2}

/-- The open set of the cover containing the edges `F₁ = {w 1 = 0}` and `F₂ = {w 2 = 0}`. -/
def circleV : Set (boundarySpace 2) := {x | circleWeight x 1 < 1/2 ∨ circleWeight x 2 < 1/2}

theorem mem_circleU {x : boundarySpace 2} : x ∈ circleU ↔ circleWeight x 0 < 1/2 := Iff.rfl

theorem mem_circleV {x : boundarySpace 2} :
    x ∈ circleV ↔ circleWeight x 1 < 1/2 ∨ circleWeight x 2 < 1/2 := Iff.rfl

theorem isOpen_circleU : IsOpen circleU :=
  isOpen_lt ((Convexity.StdSimplex.continuous_weights_apply ℝ (0 : Fin 3)).comp
    continuous_subtype_val) continuous_const

theorem isOpen_circleV : IsOpen circleV :=
  (isOpen_lt ((Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 3)).comp
      continuous_subtype_val) continuous_const).union
    (isOpen_lt ((Convexity.StdSimplex.continuous_weights_apply ℝ (2 : Fin 3)).comp
      continuous_subtype_val) continuous_const)

theorem circleU_union_circleV : circleU ∪ circleV = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_contra h
  rw [Set.mem_union, not_or] at h
  obtain ⟨h0, h1⟩ := h
  rw [mem_circleU] at h0
  rw [mem_circleV] at h1
  push_neg at h0 h1
  have hs := circleWeight_sum x
  linarith [h0, h1.1, h1.2]

/-- In `∂Δ²` no point has all three barycentric coordinates `< 1/2`. -/
theorem not_circleWeight_all_lt (x : boundarySpace 2) :
    ¬ (circleWeight x 0 < 1/2 ∧ circleWeight x 1 < 1/2 ∧ circleWeight x 2 < 1/2) := by
  intro h
  obtain ⟨i, hi⟩ := circleWeight_exists_zero x
  have hs := circleWeight_sum x
  fin_cases i
  · have hi' : circleWeight x 0 = 0 := hi
    linarith [hi', hs, h.2.1, h.2.2]
  · have hi' : circleWeight x 1 = 0 := hi
    linarith [hi', hs, h.1, h.2.2]
  · have hi' : circleWeight x 2 = 0 := hi
    linarith [hi', hs, h.1, h.2.1]

/-! ## The vertices of `∂Δ²` -/

/-- **The `i`-th vertex of `∂Δ²`**, as a point. -/
def circleVertex (i : Fin 3) : boundarySpace 2 :=
  ⟨Convexity.StdSimplex.single i, i + 1, by simp [Convexity.StdSimplex.weights_single]⟩

theorem circleWeight_circleVertex_self (i : Fin 3) : circleWeight (circleVertex i) i = 1 := by
  show (fun₀ | i => (1 : ℝ)) i = 1
  simp

theorem circleWeight_circleVertex_of_ne {i j : Fin 3} (h : j ≠ i) :
    circleWeight (circleVertex i) j = 0 := by
  show (fun₀ | i => (1 : ℝ)) j = 0
  exact Finsupp.single_eq_of_ne h

theorem circleVertex_ne (i j : Fin 3) (h : i ≠ j) : circleVertex i ≠ circleVertex j := by
  intro hc
  have h1 : circleWeight (circleVertex i) j = circleWeight (circleVertex j) j := by rw [hc]
  rw [circleWeight_circleVertex_self j, circleWeight_circleVertex_of_ne (Ne.symm h)] at h1
  exact one_ne_zero h1.symm

theorem circleVertex_one_mem_circleU : circleVertex 1 ∈ circleU := by
  rw [mem_circleU, circleWeight_circleVertex_of_ne (by decide : (0 : Fin 3) ≠ 1)]
  norm_num

theorem circleVertex_two_mem_circleU : circleVertex 2 ∈ circleU := by
  rw [mem_circleU, circleWeight_circleVertex_of_ne (by decide : (0 : Fin 3) ≠ 2)]
  norm_num

theorem circleVertex_zero_mem_circleV : circleVertex 0 ∈ circleV := by
  rw [mem_circleV, circleWeight_circleVertex_of_ne (by decide : (1 : Fin 3) ≠ 0)]
  norm_num

theorem circleVertex_one_mem_circleV : circleVertex 1 ∈ circleV := by
  rw [mem_circleV, circleWeight_circleVertex_of_ne (by decide : (2 : Fin 3) ≠ 1)]
  norm_num

theorem circleVertex_two_mem_circleV : circleVertex 2 ∈ circleV := by
  rw [mem_circleV, circleWeight_circleVertex_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  norm_num

theorem circleVertex_one_mem_inter : circleVertex 1 ∈ circleU ∩ circleV :=
  ⟨circleVertex_one_mem_circleU, circleVertex_one_mem_circleV⟩

theorem circleVertex_two_mem_inter : circleVertex 2 ∈ circleU ∩ circleV :=
  ⟨circleVertex_two_mem_circleU, circleVertex_two_mem_circleV⟩

/-- The point `v₁` of `∂Δ²`, as a point of `circleU ∩ circleV`. -/
def circleInterV1 : ↥(circleU ∩ circleV) := ⟨circleVertex 1, circleVertex_one_mem_inter⟩

/-- The point `v₂` of `∂Δ²`, as a point of `circleU ∩ circleV`. -/
def circleInterV2 : ↥(circleU ∩ circleV) := ⟨circleVertex 2, circleVertex_two_mem_inter⟩

/-- On the intersection of the two open sets of the cover, the two coordinates `w 1` and `w 2`
never agree: this is what separates the vertices `v₁` and `v₂`. -/
theorem circleWeight_one_ne_two {x : boundarySpace 2} (hx : x ∈ circleU ∩ circleV) :
    circleWeight x 1 ≠ circleWeight x 2 := by
  intro h
  obtain ⟨i, hi⟩ := circleWeight_exists_zero x
  have hs := circleWeight_sum x
  rw [Set.mem_inter_iff, mem_circleU] at hx
  have hV := hx.2
  rw [mem_circleV] at hV
  fin_cases i
  · have hi' : circleWeight x 0 = 0 := hi
    rcases hV with hV | hV <;> linarith
  · have hi' : circleWeight x 1 = 0 := hi
    linarith [hx.1]
  · have hi' : circleWeight x 2 = 0 := hi
    linarith [hx.1]

/-- **`v₁` and `v₂` are not joined by a path in `circleU ∩ circleV`.** -/
theorem not_joined_circleInterV1V2 : ¬ Joined circleInterV1 circleInterV2 := by
  rintro ⟨p⟩
  have hcont : Continuous fun t : unitInterval =>
      circleWeight ((p t : ↥(circleU ∩ circleV)) : boundarySpace 2) 1
        - circleWeight ((p t : ↥(circleU ∩ circleV)) : boundarySpace 2) 2 := by
    refine Continuous.sub ?_ ?_ <;>
      exact ((Convexity.StdSimplex.continuous_weights_apply ℝ _).comp
        continuous_subtype_val).comp (continuous_subtype_val.comp p.continuous)
  have h0 : circleWeight ((p 0 : ↥(circleU ∩ circleV)) : boundarySpace 2) 1
      - circleWeight ((p 0 : ↥(circleU ∩ circleV)) : boundarySpace 2) 2 = 1 := by
    rw [show p 0 = circleInterV1 from p.source]
    show circleWeight (circleVertex 1) 1 - circleWeight (circleVertex 1) 2 = 1
    rw [circleWeight_circleVertex_self, circleWeight_circleVertex_of_ne (by decide : (2 : Fin 3) ≠ 1)]
    norm_num
  have h1 : circleWeight ((p 1 : ↥(circleU ∩ circleV)) : boundarySpace 2) 1
      - circleWeight ((p 1 : ↥(circleU ∩ circleV)) : boundarySpace 2) 2 = -1 := by
    rw [show p 1 = circleInterV2 from p.target]
    show circleWeight (circleVertex 2) 1 - circleWeight (circleVertex 2) 2 = -1
    rw [circleWeight_circleVertex_self, circleWeight_circleVertex_of_ne (by decide : (1 : Fin 3) ≠ 2)]
    norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (circleWeight ((p 1 : ↥(circleU ∩ circleV)) : boundarySpace 2) 1
      - circleWeight ((p 1 : ↥(circleU ∩ circleV)) : boundarySpace 2) 2)
      (circleWeight ((p 0 : ↥(circleU ∩ circleV)) : boundarySpace 2) 1
      - circleWeight ((p 0 : ↥(circleU ∩ circleV)) : boundarySpace 2) 2) := by
    rw [h0, h1]
    norm_num
  obtain ⟨t, -, ht⟩ := (intermediate_value_Icc' (a := (0 : unitInterval))
    (b := (1 : unitInterval)) zero_le_one hcont.continuousOn) hmem
  exact circleWeight_one_ne_two (p t).2 (by linarith)

/-- The `0`-simplices at `v₁` and `v₂` lie in different path components of `circleU ∩ circleV`. -/
theorem piZero_mk_simplexPoint_ne :
    SSet.π₀.mk (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV1)
      ≠ SSet.π₀.mk (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV2) := by
  intro h
  have h3 : ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv
        (X := TopCat.of ↥(circleU ∩ circleV)) (simplexPoint circleInterV1))
      = ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv
        (X := TopCat.of ↥(circleU ∩ circleV)) (simplexPoint circleInterV2)) := by
    have h4 := congrArg TopCat.zerothHomotopyEquiv.symm h
    rw [TopCat.zerothHomotopyEquiv_symm_mk, TopCat.zerothHomotopyEquiv_symm_mk] at h4
    exact h4
  simp only [toSSetObj₀Equiv_simplexPoint] at h3
  exact not_joined_circleInterV1V2 (Quotient.exact h3)
/-! ## The faces of `∂Δ²` and their smallness for the cover -/

/-- The `i`-th face of `∂Δ²` lies in the closed set where the `i`-th coordinate vanishes, and this
is what makes it small for the cover. -/
theorem circleWeight_simplexFaceToBoundary_self (i : Fin 3)
    (w : Convexity.StdSimplex ℝ (Fin 2)) :
    circleWeight (simplexFaceToBoundary 1 i w) i = 0 :=
  weights_simplexFace_self 1 i w

theorem circleWeight_simplexFaceToBoundaryCM_self (i : Fin 3)
    (w : Convexity.StdSimplex ℝ (Fin 2)) :
    circleWeight (simplexFaceToBoundaryCM 1 i w) i = 0 :=
  weights_simplexFace_self 1 i w

theorem circleFace0_mem_circleU (z : Convexity.StdSimplex ℝ (Fin 2)) :
    TopCat.toSSetObjEquiv (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
      (simplexBoundaryFaceSimplex 1 0) z ∈ circleU := by
  rw [mem_circleU, toSSetObjEquiv_simplexOf]
  rw [circleWeight_simplexFaceToBoundaryCM_self]
  norm_num

theorem circleFace1_mem_circleV (z : Convexity.StdSimplex ℝ (Fin 2)) :
    TopCat.toSSetObjEquiv (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
      (simplexBoundaryFaceSimplex 1 1) z ∈ circleV := by
  rw [mem_circleV, toSSetObjEquiv_simplexOf]
  exact Or.inl (by rw [circleWeight_simplexFaceToBoundaryCM_self]; norm_num)

theorem circleFace2_mem_circleV (z : Convexity.StdSimplex ℝ (Fin 2)) :
    TopCat.toSSetObjEquiv (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
      (simplexBoundaryFaceSimplex 1 2) z ∈ circleV := by
  rw [mem_circleV, toSSetObjEquiv_simplexOf]
  exact Or.inr (by rw [circleWeight_simplexFaceToBoundaryCM_self]; norm_num)

theorem circleFace0_isSmall :
    Work.Cohomology.IsSmall circleU circleV (simplexBoundaryFaceSimplex 1 0) := by
  left
  rintro y ⟨z, rfl⟩
  show Work.Homology.toSSetObjEquiv' (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
    (simplexBoundaryFaceSimplex 1 0) z ∈ circleU
  rw [Work.Homology.toSSetObjEquiv'_apply]
  exact circleFace0_mem_circleU _

theorem circleFace1_isSmall :
    Work.Cohomology.IsSmall circleU circleV (simplexBoundaryFaceSimplex 1 1) := by
  right
  rintro y ⟨z, rfl⟩
  show Work.Homology.toSSetObjEquiv' (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
    (simplexBoundaryFaceSimplex 1 1) z ∈ circleV
  rw [Work.Homology.toSSetObjEquiv'_apply]
  exact circleFace1_mem_circleV _

theorem circleFace2_isSmall :
    Work.Cohomology.IsSmall circleU circleV (simplexBoundaryFaceSimplex 1 2) := by
  right
  rintro y ⟨z, rfl⟩
  show Work.Homology.toSSetObjEquiv' (boundarySpace 2) (Opposite.op (SimplexCategory.mk 1))
    (simplexBoundaryFaceSimplex 1 2) z ∈ circleV
  rw [Work.Homology.toSSetObjEquiv'_apply]
  exact circleFace2_mem_circleV _

/-! ## The chains `x_U`, `x_V`, `x₃` and `x₁` -/

/-- **The `U`-part of the fundamental cycle**: the chain of the edge `F₀ = [v₁,v₂]`, which lies in
`circleU`, lifted to the subspace. -/
def circleUChain : Work.Homology.ZMod ⟶
    (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleU)).X 1 :=
  SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleU))
    (Work.Homology.liftSimplex (simplexBoundaryFaceSimplex 1 0) circleFace0_mem_circleU)

/-- **The `V`-part of the fundamental cycle**: the chain `F₁ - F₂`, all of which lies in
`circleV`, lifted to the subspace. -/
def circleVChain : Work.Homology.ZMod ⟶
    (Work.Cohomology.singularChains ℤ (TopCat.of ↥circleV)).X 1 :=
  SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
      (Work.Homology.liftSimplex (simplexBoundaryFaceSimplex 1 1) circleFace1_mem_circleV)
    - SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥circleV))
      (Work.Homology.liftSimplex (simplexBoundaryFaceSimplex 1 2) circleFace2_mem_circleV)

/-- **The fundamental cycle as a small chain**: `x₃ = F₀ - F₁ + F₂`. -/
def circleSmallChain : Work.Homology.ZMod ⟶
    (Work.Cohomology.smallChains circleU circleV).X 1 :=
  (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
      ⟨simplexBoundaryFaceSimplex 1 0, circleFace0_isSmall⟩
    - (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
      ⟨simplexBoundaryFaceSimplex 1 1, circleFace1_isSmall⟩
    + (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
      ⟨simplexBoundaryFaceSimplex 1 2, circleFace2_isSmall⟩

/-- **The `0`-chain `x₁ = [v₂] - [v₁]`** in the intersection of the two open sets. -/
def circleIntersectionChain : Work.Homology.ZMod ⟶
    (Work.Cohomology.singularChains ℤ (TopCat.of ↥(circleU ∩ circleV))).X 0 :=
  SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥(circleU ∩ circleV)))
      (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV2)
    - SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of ↥(circleU ∩ circleV)))
      (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV)) circleInterV1)

/-- **The functional `H₀(circleU ∩ circleV) ⟶ ℤ`** which reads off the coefficient of the
component of `v₂`. -/
def circlePsi :
    (Work.Cohomology.singularChains ℤ (TopCat.of ↥(circleU ∩ circleV))).homology 0
      ⟶ Work.Homology.ZMod := by
  classical
  exact (SSet.homology₀Iso (TopCat.toSSet.obj (TopCat.of ↥(circleU ∩ circleV)))
      Work.Homology.ZMod).hom
    ≫ Sigma.desc (fun c => if c = SSet.π₀.mk (simplexPoint (X := TopCat.of ↥(circleU ∩ circleV))
        circleInterV2) then 𝟙 Work.Homology.ZMod else 0)

theorem circleIntersectionChain_cycle :
    circleIntersectionChain ≫
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥(circleU ∩ circleV))).d 0
          ((ComplexShape.down ℕ).next 0) = 0 := by
  have hnext : (ComplexShape.down ℕ).next 0 = 0 :=
    ComplexShape.next_eq_self' _ 0 (fun k hk => by simp [ComplexShape.down_Rel] at hk)
  rw [hnext]
  simp

theorem circleSmallChainFace_smallToSing (i : Fin 3)
    (h : Work.Cohomology.IsSmall circleU circleV (simplexBoundaryFaceSimplex 1 i)) :
    (Work.Cohomology.smallSSet circleU circleV).ιChainComplex
        ⟨simplexBoundaryFaceSimplex 1 i, h⟩
      ≫ (Work.Cohomology.smallToSing circleU circleV).f 1
      = simplexBoundaryFaceChain 1 i := by
  rw [show Work.Cohomology.smallToSing circleU circleV
      = SSet.chainComplexMap (Work.Cohomology.smallSubcomplex circleU circleV).ι
          (ModuleCat.of ℤ ℤ) from rfl]
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- The small chain `x₃` maps to the fundamental cycle `z₁` in the chains of `∂Δ²`. -/
theorem circleSmallChain_smallToSing :
    circleSmallChain ≫ (Work.Cohomology.smallToSing circleU circleV).f 1
      = simplexBoundaryChain 1 := by
  rw [circleSmallChain, Preadditive.add_comp, Preadditive.sub_comp,
    circleSmallChainFace_smallToSing 0 circleFace0_isSmall,
    circleSmallChainFace_smallToSing 1 circleFace1_isSmall,
    circleSmallChainFace_smallToSing 2 circleFace2_isSmall]
  rw [simplexBoundaryChain, Fin.sum_univ_three]
  norm_num [sub_eq_add_neg]

/-- The small chain `x₃` is a cycle. -/
theorem circleSmallChain_cycle :
    circleSmallChain ≫ (Work.Cohomology.smallChains circleU circleV).d 1 0 = 0 := by
  have hmono : Mono ((Work.Cohomology.smallToSing circleU circleV).f 0) :=
    (ModuleCat.mono_iff_injective _).2
      (Work.Cohomology.smallToSing_f_injective circleU circleV 0)
  rw [← cancel_mono ((Work.Cohomology.smallToSing circleU circleV).f 0), Limits.zero_comp,
    Category.assoc,
    ← HomologicalComplex.Hom.comm (Work.Cohomology.smallToSing circleU circleV) 1 0,
    ← Category.assoc, circleSmallChain_smallToSing]
  have h := simplexBoundaryChain_d 1
  rw [show (ComplexShape.down ℕ).next 1 = 0 from ChainComplex.next_nat_succ 0] at h
  exact h

end

end Work.HomologyExtra
