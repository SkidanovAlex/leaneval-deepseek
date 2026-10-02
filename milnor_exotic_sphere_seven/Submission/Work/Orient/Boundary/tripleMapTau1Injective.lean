import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# (I) The map of relative homology of the pairs `(∂W, ∂W∖{y}) → (B', B'∖{y})` is injective

For the coordinate half-ball `K = halfBallPiece (n+1) W y r` around a boundary point `y`, and
`B' = (K ∩ W°)ᶜ = ∂W ∪ (W∖K)`, `A' = B'∖{y}`, the map

`e : H_n(∂W, ∂W∖{y}) ⟶ H_n(B', A')`

induced by the inclusion of pairs is an isomorphism: both pairs agree on the small open half-ball
`U = smallBall n W y r ⊆ K` containing `y` (there `∂W ∩ U = B' ∩ U`), and excision in the two
subspaces `↥∂W` and `↥B'` identifies both groups with the same small model.

The proof is assembled from

* `Work.Cohomology.cokerInclSubIso` — the canonical isomorphism between the two models of the
  relative chain complex of a pair (`coker (inclChainsSub M A B h)` and the subspace model);
* `Work.Cohomology.cokerInclSubIso_natural` — its naturality with respect to inclusions of pairs;
* the excision isomorphism `Work.Cohomology.excision_relChainsMap_isIso` in the two subspaces;
* the canonical homeomorphism `↥{z : ↥∂W | z ∈ U} ≃ₜ ↥{z : ↥B' | z ∈ U}`.

See the docstring of `tripleMap_tau1_injective` for the diagram.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Cohomology

noncomputable section

/-! ## 1. Proof irrelevance for compatibility arguments -/

/-- The compatibility argument of `cokernel.map` does not matter. -/
theorem cokernel_map_proof_irrel {C : Type*} [Category C] [HasZeroMorphisms C] {X Y X' Y' : C}
    (f : X ⟶ Y) [HasCokernel f] (f' : X' ⟶ Y') [HasCokernel f']
    (p : X ⟶ X') (q : Y ⟶ Y') (w w' : f ≫ q = p ≫ f') :
    cokernel.map f f' p q w = cokernel.map f f' p q w' :=
  congrArg (fun v => cokernel.map f f' p q v) (Subsingleton.elim w w')

/-- The compatibility argument of `relChainsMapOf` does not matter. -/
theorem relChainsMapOf_proof_irrel {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w w' : subtypeIncl X A ≫ f = g ≫ subtypeIncl Y B) :
    relChainsMapOf X Y A B f g w = relChainsMapOf X Y A B f g w' := by
  unfold relChainsMapOf
  exact cokernel_map_proof_irrel _ _ _ _ _ _

/-! ## 2. The two models of the relative chain complex of a pair -/

/-- The inclusion of subset spaces, as a morphism of `TopCat`. -/
def inclSub {M : TopCat} {A B : Set M} (h : A ⊆ B) : TopCat.of ↥A ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun z => ⟨(z : M), h z.2⟩,
    Continuous.subtype_mk (f := fun z : ↥A => (z : M)) continuous_subtype_val (fun z => h z.2)⟩

/-- `inclChainsSub` is the chain map induced by `inclSub`. -/
theorem inclChainsSub_eq_chainMap (M : TopCat) (A B : Set M) (h : A ⊆ B) :
    inclChainsSub M A B h = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B) (inclSub h) := rfl

/-- The canonical homeomorphism `↥A ≃ₜ ↥{y : ↥B | (y : M) ∈ A}`. -/
def subSetHomeo {M : TopCat} {A B : Set M} (h : A ⊆ B) :
    ↥A ≃ₜ ↥{y : ↥B | (y : M) ∈ A} where
  toFun a := ⟨⟨(a : M), h a.2⟩, a.2⟩
  invFun b := ⟨(b.1 : M), b.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun a => h a.2)) (fun a => a.2)
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun b => b.2)

/-- The square relating `inclChainsSub` with the canonical homeomorphism. -/
theorem inclChainsSub_eq_mapIso_comp {M : TopCat} {A B : Set M} (h : A ⊆ B) :
    inclChainsSub M A B h
      = (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
          (TopCat.isoOfHomeo (subSetHomeo h))).hom
        ≫ inclChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A} := by
  have hmap : inclSub h = (TopCat.isoOfHomeo (subSetHomeo h)).hom
      ≫ subtypeIncl (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A} := by
    ext z; rfl
  rw [inclChainsSub_eq_chainMap M A B h]
  rw [show (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (subSetHomeo h))).hom
      = chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥{y : ↥B | (y : M) ∈ A})
        (TopCat.isoOfHomeo (subSetHomeo h)).hom from rfl]
  rw [show inclChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}
      = chainMap ℤ (TopCat.of ↥{y : ↥B | (y : M) ∈ A}) (TopCat.of ↥B)
        (subtypeIncl (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}) from rfl]
  rw [← Functor.map_comp, hmap]

/-- The square of `inclChainsSub` with the canonical homeomorphism, in the form whose right hand
side ends with the identity of the target (the form consumed by `cokernel.mapIso`). -/
theorem inclChainsSub_eq_mapIso_comp_refl {M : TopCat} {A B : Set M} (h : A ⊆ B) :
    inclChainsSub M A B h ≫ (Iso.refl (singularChains ℤ (TopCat.of ↥B))).hom
      = (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
          (TopCat.isoOfHomeo (subSetHomeo h))).hom
        ≫ inclChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A} := by
  rw [Iso.refl_hom, Category.comp_id, inclChainsSub_eq_mapIso_comp h]

/-- **The two models of the relative chain complex of a pair `(B,A)`**: the "restricted inclusion"
model `coker (inclChainsSub M A B h)` and the "subspace" model
`relChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}` are canonically isomorphic. -/
noncomputable def cokerInclSubIso {M : TopCat} {A B : Set M} (h : A ⊆ B) :
    cokernel (inclChainsSub M A B h) ≅
      cokernel (inclChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A}) :=
  cokernel.mapIso (f := inclChainsSub M A B h)
    (inclChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A})
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo (subSetHomeo h)))
    (Iso.refl _) (inclChainsSub_eq_mapIso_comp_refl h)

/-! ## 3. The map of the subspace models induced by an inclusion of pairs -/

/-- The map of the two "subspace" models induced by an inclusion of pairs `(A,B) ⊆ (A',B')`.  It is
the map of `TopCat`-spaces `↥B → ↥B'` given by the identity on `M` together with the induced map on
the subspace `↥{y : ↥B | (y : M) ∈ A}`. -/
def inclPairSub {M : TopCat} {A B A' B' : Set M} (hA : A ⊆ A') (hB : B ⊆ B') :
    TopCat.of ↥{y : ↥B | (y : M) ∈ A} ⟶ TopCat.of ↥{y : ↥B' | (y : M) ∈ A'} :=
  TopCat.ofHom ⟨fun z => ⟨⟨(z.1.1 : M), hB z.1.2⟩, hA z.2⟩,
    Continuous.subtype_mk
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
        (fun z => hB z.1.2)) (fun z => hA z.2)⟩

/-- The compatibility of `inclSub` and `inclPairSub`. -/
theorem inclPairSub_compat {M : TopCat} {A B A' B' : Set M} (hA : A ⊆ A') (hB : B ⊆ B') :
    subtypeIncl (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A} ≫ inclSub hB
      = inclPairSub hA hB ≫ subtypeIncl (TopCat.of ↥B') {y : ↥B' | (y : M) ∈ A'} := by
  ext z; rfl

/-- **The map of the subspace models induced by an inclusion of pairs.** -/
def relPairMap {M : TopCat} {A B A' B' : Set M} (hA : A ⊆ A') (hB : B ⊆ B') :
    relChains (TopCat.of ↥B) {y : ↥B | (y : M) ∈ A} ⟶
      relChains (TopCat.of ↥B') {y : ↥B' | (y : M) ∈ A'} :=
  relChainsMapOf (TopCat.of ↥B) (TopCat.of ↥B') {y : ↥B | (y : M) ∈ A}
    {y : ↥B' | (y : M) ∈ A'} (inclSub hB) (inclPairSub hA hB) (inclPairSub_compat hA hB)

/-! ## 4. Naturality of `cokerInclSubIso` -/

/-- **Naturality of the passage between the two models of the relative chain complex of a pair.**
For `S ⊆ T ⊆ M` and `S₂ ⊆ T₂ ⊆ M` with `S ⊆ S₂`, `T ⊆ T₂` the square

`coker (C(T)/C(S)) --⟶ coker (C(T₂)/C(S₂))`
`     ↓                                  ↓`
`C(T,S)             --⟶  C(T₂,S₂)`

commutes, where the vertical maps are `cokerInclSubIso` and the horizontal ones are induced by the
inclusions of pairs. -/
theorem cokerInclSubIso_natural {M : TopCat} {S T S₂ T₂ : Set M}
    (hST : S ⊆ T) (hS₂T₂ : S₂ ⊆ T₂) (hSS₂ : S ⊆ S₂) (hTT₂ : T ⊆ T₂) :
    (cokerInclSubIso hST).hom ≫ relPairMap (A := S) (B := T) (A' := S₂) (B' := T₂) hSS₂ hTT₂
      = cokernel.map (inclChainsSub M S T hST) (inclChainsSub M S₂ T₂ hS₂T₂)
          (inclChainsSub M S S₂ hSS₂) (inclChainsSub M T T₂ hTT₂)
          (Work.Orient.Boundary.tripleCompat hST hS₂T₂ hSS₂ hTT₂)
        ≫ (cokerInclSubIso hS₂T₂).hom := by
  apply (cancel_epi (cokernel.π (inclChainsSub M S T hST))).mp
  have hA : cokernel.π (inclChainsSub M S T hST) ≫ (cokerInclSubIso hST).hom
      = cokernel.π (inclChains (TopCat.of ↥T) {y : ↥T | (y : M) ∈ S}) := by
    unfold cokerInclSubIso
    rw [cokernel.mapIso_hom, cokernel_π_map]
    simp
  have hB : cokernel.π (inclChains (TopCat.of ↥T) {y : ↥T | (y : M) ∈ S})
      ≫ relPairMap (A := S) (B := T) (A' := S₂) (B' := T₂) hSS₂ hTT₂
      = chainMap ℤ (TopCat.of ↥T) (TopCat.of ↥T₂) (inclSub hTT₂)
        ≫ cokernel.π (inclChains (TopCat.of ↥T₂) {y : ↥T₂ | (y : M) ∈ S₂}) := by
    unfold relPairMap
    rw [relChainsMapOf, cokernel_π_map]
  have hC : cokernel.π (inclChainsSub M S T hST)
      ≫ cokernel.map (inclChainsSub M S T hST) (inclChainsSub M S₂ T₂ hS₂T₂)
          (inclChainsSub M S S₂ hSS₂) (inclChainsSub M T T₂ hTT₂)
          (Work.Orient.Boundary.tripleCompat hST hS₂T₂ hSS₂ hTT₂)
      = inclChainsSub M T T₂ hTT₂ ≫ cokernel.π (inclChainsSub M S₂ T₂ hS₂T₂) :=
    cokernel_π_map _ _ _ _ _
  have hD : cokernel.π (inclChainsSub M S₂ T₂ hS₂T₂) ≫ (cokerInclSubIso hS₂T₂).hom
      = cokernel.π (inclChains (TopCat.of ↥T₂) {y : ↥T₂ | (y : M) ∈ S₂}) := by
    unfold cokerInclSubIso
    rw [cokernel.mapIso_hom, cokernel_π_map]
    simp
  have hLHS : cokernel.π (inclChainsSub M S T hST)
      ≫ ((cokerInclSubIso hST).hom
          ≫ relPairMap (A := S) (B := T) (A' := S₂) (B' := T₂) hSS₂ hTT₂)
      = chainMap ℤ (TopCat.of ↥T) (TopCat.of ↥T₂) (inclSub hTT₂)
        ≫ cokernel.π (inclChains (TopCat.of ↥T₂) {y : ↥T₂ | (y : M) ∈ S₂}) := by
    rw [← Category.assoc, hA, hB]
  have hRHS : cokernel.π (inclChainsSub M S T hST)
      ≫ (cokernel.map (inclChainsSub M S T hST) (inclChainsSub M S₂ T₂ hS₂T₂)
          (inclChainsSub M S S₂ hSS₂) (inclChainsSub M T T₂ hTT₂)
          (Work.Orient.Boundary.tripleCompat hST hS₂T₂ hSS₂ hTT₂)
        ≫ (cokerInclSubIso hS₂T₂).hom)
      = chainMap ℤ (TopCat.of ↥T) (TopCat.of ↥T₂) (inclSub hTT₂)
        ≫ cokernel.π (inclChains (TopCat.of ↥T₂) {y : ↥T₂ | (y : M) ∈ S₂}) := by
    rw [← Category.assoc, hC, Category.assoc, hD, inclChainsSub_eq_chainMap M T T₂ hTT₂]
  exact hLHS.trans hRHS.symm

end

end Work.Cohomology

namespace Work.Orient.Boundary

noncomputable section

/-! ## 5. The small open half-ball at a boundary point -/

/-- The small open half-ball of radius `r/2` around a boundary point `y`: the chart preimage of the
open ball of radius `r/2` around the image of `y`.  It is contained in the coordinate half-ball
`halfBallPiece (n+1) W y r` and is open. -/
abbrev smallBall (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set W :=
  (chartAt (EuclideanHalfSpace (n + 1)) y).source ∩
    (chartAt (EuclideanHalfSpace (n + 1)) y) ⁻¹'
      (Work.Orient.halfIncl (n + 1) ⁻¹'
        Metric.ball (Work.Orient.halfIncl (n + 1)
          ((chartAt (EuclideanHalfSpace (n + 1)) y) y)) (r / 2))

theorem isOpen_smallBall (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : IsOpen (smallBall n W y r) :=
  (chartAt (EuclideanHalfSpace (n + 1)) y).isOpen_inter_preimage
    (Metric.isOpen_ball.preimage (modelWithCornersEuclideanHalfSpace (n + 1)).continuous)

theorem mem_smallBall_center (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) (hr : 0 < r) : y ∈ smallBall n W y r := by
  refine ⟨mem_chart_source _ y, ?_⟩
  show Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) y) y) ∈
    Metric.ball (Work.Orient.halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) y) y))
      (r / 2)
  rw [Metric.mem_ball, dist_self]
  linarith

theorem smallBall_sub_halfBallPiece (n : ℕ) (W : TopCat)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W) (r : ℝ) :
    smallBall n W y r ⊆ Work.Orient.halfBallPiece (n + 1) W y r := by
  intro x hx
  exact ⟨Metric.ball_subset_closedBall hx.2, hx.1⟩

/-- **The two pairs agree on the small ball**: `∂W ∩ U = B' ∩ U`. -/
theorem bdrySetW_inter_smallBall (n : ℕ) (W : TopCat)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W) (r : ℝ) :
    bdrySetW n W ∩ smallBall n W y r = bigB n W y r ∩ smallBall n W y r := by
  ext z
  constructor
  · intro hz
    exact ⟨bdrySetW_sub_bigB n W y r hz.1, hz.2⟩
  · intro hz
    have hzK : z ∈ halfBallK n W y r := smallBall_sub_halfBallPiece n W y r hz.2
    have hznot : z ∉ halfBallK n W y r ∩ (bdrySetW n W)ᶜ := hz.1
    refine ⟨?_, hz.2⟩
    by_contra hzd
    exact hznot ⟨hzK, hzd⟩

/-- The punctured subspace of `↥∂W`. -/
abbrev punctT (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) : Set ↥(bdrySetW n W) := {z | (z : W) ∈ bdryMinus n W y}

/-- The small open subset of `↥∂W`. -/
abbrev smallT (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set ↥(bdrySetW n W) := {z | (z : W) ∈ smallBall n W y r}

/-- The punctured subspace of `↥B'`. -/
abbrev punctB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set ↥(bigB n W y r) := {z | (z : W) ∈ bigA n W y r}

/-- The small open subset of `↥B'`. -/
abbrev smallB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set ↥(bigB n W y r) := {z | (z : W) ∈ smallBall n W y r}

theorem isOpen_punctT (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    IsOpen (punctT n W y) := by
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  have h : punctT n W y = ({⟨y, hy⟩} : Set ↥(bdrySetW n W))ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_diff]
    constructor
    · intro hz hzy
      exact hz.2 (congrArg Subtype.val hzy)
    · intro hz
      exact ⟨z.2, fun hyz => hz (Subtype.ext hyz)⟩
  rw [h]
  exact isClosed_singleton.isOpen_compl

theorem isOpen_punctB (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (r : ℝ) :
    IsOpen (punctB n W y r) := by
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  have hyB : y ∈ bigB n W y r := bdrySetW_sub_bigB n W y r hy
  have h : punctB n W y r = ({⟨y, hyB⟩} : Set ↥(bigB n W y r))ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_diff]
    constructor
    · intro hz hzy
      exact hz.2 (congrArg Subtype.val hzy)
    · intro hz
      exact ⟨z.2, fun hyz => hz (Subtype.ext hyz)⟩
  rw [h]
  exact isClosed_singleton.isOpen_compl

end

end Work.Orient.Boundary

namespace Work.Orient.Boundary

noncomputable section

/-! ## 6. The small relative complexes and the excision maps -/

/-- The punctured part of the small piece, as a subset of the small piece `↥smallT`. -/
abbrev smallTp (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set ↥(smallT n W y r) :=
  {z | ((z : ↥(smallT n W y r)) : ↥(bdrySetW n W)) ∈ punctT n W y}

/-- The punctured part of the small piece, as a subset of the small piece `↥smallB`. -/
abbrev smallBp (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set ↥(smallB n W y r) :=
  {z | ((z : ↥(smallB n W y r)) : ↥(bigB n W y r)) ∈ punctB n W y r}

/-- The compatibility square of the inclusion of the small piece into `↥∂W`. -/
theorem compatT (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r)
      = Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (punctT n W y) := by
  ext z; rfl

/-- The compatibility square of the inclusion of the small piece into `↥B'`. -/
theorem compatB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥(smallB n W y r)) (smallBp n W y r)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r)
      = Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r) (punctB n W y r)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (punctB n W y r) := by
  ext z; rfl

/-- The excision map `H_n(∂W, ∂W∖{y}) → H_n(small, small∖{y})` in the subspace model. -/
noncomputable def excT (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.relChains (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
      ⟶ Work.Cohomology.relChains (TopCat.of ↥(bdrySetW n W)) (punctT n W y) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(smallT n W y r)) (TopCat.of ↥(bdrySetW n W))
    (smallTp n W y r) (punctT n W y)
    (Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r))
    (Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y))
    (compatT n W y r)

/-- The excision map `H_n(B', B'∖{y}) → H_n(small, small∖{y})` in the subspace model. -/
noncomputable def excB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.relChains (TopCat.of ↥(smallB n W y r)) (smallBp n W y r)
      ⟶ Work.Cohomology.relChains (TopCat.of ↥(bigB n W y r)) (punctB n W y r) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(smallB n W y r)) (TopCat.of ↥(bigB n W y r))
    (smallBp n W y r) (punctB n W y r)
    (Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r))
    (Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r) (punctB n W y r))
    (compatB n W y r)

/-- `excT` is the excision map `relChainsMap`. -/
theorem excT_eq (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.relChainsMap (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
      = excT n W y r := by
  unfold Work.Cohomology.relChainsMap excT
  exact Work.Cohomology.relChainsMapOf_proof_irrel _ _ _ _ _ _

/-- `excB` is the excision map `relChainsMap`. -/
theorem excB_eq (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.relChainsMap (TopCat.of ↥(bigB n W y r)) (smallB n W y r) (punctB n W y r)
      = excB n W y r := by
  unfold Work.Cohomology.relChainsMap excB
  exact Work.Cohomology.relChainsMapOf_proof_irrel _ _ _ _ _ _

end

end Work.Orient.Boundary

namespace Work.Orient.Boundary

noncomputable section

/-! ## 7. The two small pieces are canonically the same -/

theorem mem_bdrySetW_of_mem_smallBall (n : ℕ) (W : TopCat)
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W) (r : ℝ)
    (z : ↥(bigB n W y r)) (hz : (z : W) ∈ smallBall n W y r) :
    (z : W) ∈ bdrySetW n W := by
  have h1 : (z : W) ∈ bdrySetW n W ∩ smallBall n W y r := by
    rw [bdrySetW_inter_smallBall n W y r]
    exact ⟨z.2, hz⟩
  exact h1.1

/-- The canonical homeomorphism between the two small pieces. -/
abbrev smallHomeo (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : ↥(smallT n W y r) ≃ₜ ↥(smallB n W y r) where
  toFun z := ⟨⟨(z.1.1 : W), bdrySetW_sub_bigB n W y r z.1.2⟩, z.2⟩
  invFun z := ⟨⟨(z.1.1 : W), mem_bdrySetW_of_mem_smallBall n W y r z.1 z.2⟩, z.2⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk (f := fun z : ↥(smallT n W y r) => (z.1.1 : W))
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => bdrySetW_sub_bigB n W y r z.1.2)) (fun z => z.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk (f := fun z : ↥(smallB n W y r) => (z.1.1 : W))
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => mem_bdrySetW_of_mem_smallBall n W y r z.1 z.2)) (fun z => z.2)

theorem smallHomeo_mem (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) (z : ↥(smallT n W y r)) :
    (z ∈ smallTp n W y r ↔ smallHomeo n W y r z ∈ smallBp n W y r) := by
  have hz : ((smallHomeo n W y r z : ↥(smallB n W y r)) : W) = ((z : ↥(smallT n W y r)) : W) :=
    rfl
  simp only [smallTp, smallBp, punctT, punctB, bigA, bdryMinus, Set.mem_setOf_eq,
    Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, hz]
  constructor
  · intro h; exact ⟨bdrySetW_sub_bigB n W y r h.1, h.2⟩
  · intro h; exact ⟨z.1.2, h.2⟩

/-- The induced homeomorphism of the punctured small pieces. -/
def smallHomeoPunct (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : ↥(smallTp n W y r) ≃ₜ ↥(smallBp n W y r) :=
  homeomorphRestrict (smallHomeo n W y r) (smallTp n W y r) (smallBp n W y r)
    (smallHomeo_mem n W y r)

/-- The map of `TopCat` induced by the canonical homeomorphism of the small pieces. -/
def smallTop (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : TopCat.of ↥(smallT n W y r) ⟶ TopCat.of ↥(smallB n W y r) :=
  TopCat.ofHom (smallHomeo n W y r).toHomotopyEquiv.toFun

/-- The map of `TopCat` induced by the induced homeomorphism of the punctured small pieces. -/
def smallPunctTop (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : TopCat.of ↥(smallTp n W y r) ⟶ TopCat.of ↥(smallBp n W y r) :=
  TopCat.ofHom (smallHomeoPunct n W y r).toHomotopyEquiv.toFun

/-- The compatibility of `smallHomeo` with the inclusions of the punctured pieces. -/
theorem smallHomeo_compat (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
        ≫ smallTop n W y r
      = smallPunctTop n W y r
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(smallB n W y r)) (smallBp n W y r) := by
  ext z; rfl

theorem smallTop_chainMap (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(smallT n W y r)) (TopCat.of ↥(smallB n W y r)) (smallTop n W y r)) k) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of ↥(smallT n W y r)) (Y := TopCat.of ↥(smallB n W y r))
    (smallHomeo n W y r).toHomotopyEquiv k

theorem smallPunctTop_chainMap (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(smallTp n W y r)) (TopCat.of ↥(smallBp n W y r)) (smallPunctTop n W y r)) k) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of ↥(smallTp n W y r)) (Y := TopCat.of ↥(smallBp n W y r))
    (smallHomeoPunct n W y r).toHomotopyEquiv k

/-- The map between the two small models, as a chain map. -/
noncomputable def smallMap (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    Work.Cohomology.relChains (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
      ⟶ Work.Cohomology.relChains (TopCat.of ↥(smallB n W y r)) (smallBp n W y r) :=
  Work.Cohomology.relChainsMapOf (TopCat.of ↥(smallT n W y r)) (TopCat.of ↥(smallB n W y r))
    (smallTp n W y r) (smallBp n W y r) (smallTop n W y r) (smallPunctTop n W y r)
    (smallHomeo_compat n W y r)

/-- **The map between the two small models is a quasi-isomorphism.** -/
theorem smallIso (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    IsIso (HomologicalComplex.homologyMap (smallMap n W y r) n) :=
  Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of ↥(smallT n W y r))
    (Y := TopCat.of ↥(smallB n W y r)) (smallTp n W y r) (smallBp n W y r)
    (smallTop n W y r) (smallPunctTop n W y r) (smallHomeo_compat n W y r) n
    (smallTop_chainMap n W y r) (smallPunctTop_chainMap n W y r)

/-! ## 8. The target: injectivity of the comparison map on the relative homology of the pairs -/

/-- **(I)** The map `e` on the `n`-th homology induced by the inclusion of pairs
`(∂W, ∂W∖{y}) → (B', A')` is injective: `∂W` and `B'` agree on the small open half-ball `U`, so
both relative groups are identified by excision with the same small model, and `e` becomes an
isomorphism. -/
theorem tripleMap_tau1_injective (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r) :
    Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (tripleMap W (bdryMinus_sub_bdrySetW n W y)
        (bigA_sub_bigB n W y r) (bdryMinus_sub_bigA n W y r)
        (bdrySetW_sub_bigB n W y r)).τ₁ n)) := by
  classical
  haveI hT1h : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI hT1W : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  -- ## the two excisions
  have hST_open : IsOpen (punctT n W y) := isOpen_punctT n W y hy
  have hSB_open : IsOpen (punctB n W y r) := isOpen_punctB n W y hy r
  have hUT_open : IsOpen (smallT n W y r) :=
    (isOpen_smallBall n W y r).preimage continuous_subtype_val
  have hUB_open : IsOpen (smallB n W y r) :=
    (isOpen_smallBall n W y r).preimage continuous_subtype_val
  have hcovT : smallT n W y r ∪ punctT n W y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases h : (z : W) ∈ smallBall n W y r
    · exact Or.inl h
    · exact Or.inr ⟨z.2, fun hzy => h (hzy.symm ▸ mem_smallBall_center n W y r hr)⟩
  have hcovB : smallB n W y r ∪ punctB n W y r = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases h : (z : W) ∈ smallBall n W y r
    · exact Or.inl h
    · exact Or.inr ⟨z.2, fun hzy => h (hzy.symm ▸ mem_smallBall_center n W y r hr)⟩
  have hExcT : IsIso (HomologicalComplex.homologyMap (excT n W y r) n) := by
    rw [← excT_eq n W y r]
    exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of ↥(bdrySetW n W))
      (smallT n W y r) (punctT n W y) hUT_open hST_open hcovT n
  have hExcB : IsIso (HomologicalComplex.homologyMap (excB n W y r) n) := by
    rw [← excB_eq n W y r]
    exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of ↥(bigB n W y r))
      (smallB n W y r) (punctB n W y r) hUB_open hSB_open hcovB n
  -- ## the square `excT ≫ β = smallMap ≫ excB`
  have hf_eq : Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r)
        ≫ Work.Cohomology.inclSub (bdrySetW_sub_bigB n W y r)
      = smallTop n W y r
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r) := by
    ext z; rfl
  have hg_eq : Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
        ≫ Work.Cohomology.inclPairSub (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)
      = smallPunctTop n W y r
        ≫ Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r)
            (punctB n W y r) := by
    ext z; rfl
  have wL : Work.Cohomology.subtypeIncl (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
        ≫ (Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r)
            ≫ Work.Cohomology.inclSub (bdrySetW_sub_bigB n W y r))
      = (Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
            ≫ Work.Cohomology.inclPairSub (bdryMinus_sub_bigA n W y r)
                (bdrySetW_sub_bigB n W y r))
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (punctB n W y r) := by
    ext z; rfl
  have wR : Work.Cohomology.subtypeIncl (TopCat.of ↥(smallT n W y r)) (smallTp n W y r)
        ≫ (smallTop n W y r
            ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r))
      = (smallPunctTop n W y r
            ≫ Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r)
                (punctB n W y r))
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (punctB n W y r) := by
    ext z; rfl
  have hL : excT n W y r ≫ Work.Cohomology.relPairMap (A := bdryMinus n W y) (B := bdrySetW n W)
        (A' := bigA n W y r) (B' := bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)
      = Work.Cohomology.relChainsMapOf (X := TopCat.of ↥(smallT n W y r))
          (Y := TopCat.of ↥(bigB n W y r)) (smallTp n W y r) (punctB n W y r)
          (Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r)
            ≫ Work.Cohomology.inclSub (bdrySetW_sub_bigB n W y r))
          (Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
            ≫ Work.Cohomology.inclPairSub (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))
          wL := by
    unfold excT Work.Cohomology.relPairMap
    exact Work.Cohomology.relChainsMapOf_comp (X := TopCat.of ↥(smallT n W y r))
      (Y := TopCat.of ↥(bdrySetW n W)) (Z := TopCat.of ↥(bigB n W y r))
      (smallTp n W y r) (punctT n W y) (punctB n W y r)
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r))
      (Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y))
      (compatT n W y r)
      (Work.Cohomology.inclSub (bdrySetW_sub_bigB n W y r))
      (Work.Cohomology.inclPairSub (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))
      (Work.Cohomology.inclPairSub_compat (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))
      wL
  have hR : smallMap n W y r ≫ excB n W y r
      = Work.Cohomology.relChainsMapOf (X := TopCat.of ↥(smallT n W y r))
          (Y := TopCat.of ↥(bigB n W y r)) (smallTp n W y r) (punctB n W y r)
          (smallTop n W y r
            ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r))
          (smallPunctTop n W y r
            ≫ Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r)
                (punctB n W y r))
          wR := by
    unfold smallMap excB
    exact Work.Cohomology.relChainsMapOf_comp (X := TopCat.of ↥(smallT n W y r))
      (Y := TopCat.of ↥(smallB n W y r)) (Z := TopCat.of ↥(bigB n W y r))
      (smallTp n W y r) (smallBp n W y r) (punctB n W y r)
      (smallTop n W y r) (smallPunctTop n W y r) (smallHomeo_compat n W y r)
      (Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r))
      (Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r) (punctB n W y r))
      (compatB n W y r) wR
  have hC : Work.Cohomology.relChainsMapOf (X := TopCat.of ↥(smallT n W y r))
        (Y := TopCat.of ↥(bigB n W y r)) (smallTp n W y r) (punctB n W y r)
        (Work.Cohomology.subtypeIncl (TopCat.of ↥(bdrySetW n W)) (smallT n W y r)
          ≫ Work.Cohomology.inclSub (bdrySetW_sub_bigB n W y r))
        (Work.Cohomology.inclInterA (TopCat.of ↥(bdrySetW n W)) (smallT n W y r) (punctT n W y)
          ≫ Work.Cohomology.inclPairSub (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))
        wL
      = Work.Cohomology.relChainsMapOf (X := TopCat.of ↥(smallT n W y r))
        (Y := TopCat.of ↥(bigB n W y r)) (smallTp n W y r) (punctB n W y r)
        (smallTop n W y r
          ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(bigB n W y r)) (smallB n W y r))
        (smallPunctTop n W y r
          ≫ Work.Cohomology.inclInterA (TopCat.of ↥(bigB n W y r)) (smallB n W y r)
              (punctB n W y r))
        wR := by
    apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains (TopCat.of ↥(smallT n W y r))
      (smallTp n W y r)))).mp
    rw [Work.Cohomology.relChainsMapOf, Work.Cohomology.relChainsMapOf,
      Work.Cohomology.cokernel_π_map, Work.Cohomology.cokernel_π_map]
    rw [hf_eq]
  have hSq2 : excT n W y r ≫ Work.Cohomology.relPairMap (A := bdryMinus n W y) (B := bdrySetW n W)
        (A' := bigA n W y r) (B' := bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)
      = smallMap n W y r ≫ excB n W y r :=
    hL.trans (hC.trans hR.symm)
  -- ## β is an isomorphism
  have hBetaIso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relPairMap (A := bdryMinus n W y) (B := bdrySetW n W)
        (A' := bigA n W y r) (B' := bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)) n) := by
    have hh := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hSq2
    simp only [HomologicalComplex.homologyMap_comp] at hh
    haveI : IsIso (HomologicalComplex.homologyMap (excT n W y r) n) := hExcT
    haveI : IsIso (HomologicalComplex.homologyMap (excB n W y r) n) := hExcB
    haveI : IsIso (HomologicalComplex.homologyMap (smallMap n W y r) n) := smallIso n W y r
    haveI h1 : IsIso (HomologicalComplex.homologyMap (smallMap n W y r) n
        ≫ HomologicalComplex.homologyMap (excB n W y r) n) := inferInstance
    haveI h2 : IsIso (HomologicalComplex.homologyMap (excT n W y r) n
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.relPairMap (A := bdryMinus n W y)
            (B := bdrySetW n W) (A' := bigA n W y r) (B' := bigB n W y r)
            (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)) n) := by
      rw [hh]; exact h1
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (excT n W y r) n)
      (HomologicalComplex.homologyMap (Work.Cohomology.relPairMap (A := bdryMinus n W y)
        (B := bdrySetW n W) (A' := bigA n W y r) (B' := bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)) n)
  -- ## the comparison map is an isomorphism
  have hsq1 := Work.Cohomology.cokerInclSubIso_natural (M := W)
    (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
    (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)
  have hIso : IsIso (HomologicalComplex.homologyMap
      (cokernel.map (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bdrySetW n W)
          (bdryMinus_sub_bdrySetW n W y))
        (Work.Cohomology.inclChainsSub W (bigA n W y r) (bigB n W y r) (bigA_sub_bigB n W y r))
        (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bigA n W y r)
          (bdryMinus_sub_bigA n W y r))
        (Work.Cohomology.inclChainsSub W (bdrySetW n W) (bigB n W y r)
          (bdrySetW_sub_bigB n W y r))
        (Work.Orient.Boundary.tripleCompat (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
          (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))) n) := by
    have hh := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hsq1
    simp only [HomologicalComplex.homologyMap_comp] at hh
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.cokerInclSubIso (bdryMinus_sub_bdrySetW n W y)).hom n) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
        (Work.Cohomology.cokerInclSubIso (bdryMinus_sub_bdrySetW n W y)).hom
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.cokerInclSubIso (bigA_sub_bigB n W y r)).hom n) :=
      Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
        (Work.Cohomology.cokerInclSubIso (bigA_sub_bigB n W y r)).hom
    haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relPairMap
        (A := bdryMinus n W y) (B := bdrySetW n W) (A' := bigA n W y r) (B' := bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)) n) := hBetaIso
    haveI h1 : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.cokerInclSubIso (bdryMinus_sub_bdrySetW n W y)).hom n
        ≫ HomologicalComplex.homologyMap (Work.Cohomology.relPairMap (A := bdryMinus n W y)
            (B := bdrySetW n W) (A' := bigA n W y r) (B' := bigB n W y r)
            (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)) n) := inferInstance
    haveI h2 : IsIso (HomologicalComplex.homologyMap
        (cokernel.map (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bdrySetW n W)
            (bdryMinus_sub_bdrySetW n W y))
          (Work.Cohomology.inclChainsSub W (bigA n W y r) (bigB n W y r) (bigA_sub_bigB n W y r))
          (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bigA n W y r)
            (bdryMinus_sub_bigA n W y r))
          (Work.Cohomology.inclChainsSub W (bdrySetW n W) (bigB n W y r)
            (bdrySetW_sub_bigB n W y r))
          (Work.Orient.Boundary.tripleCompat (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
            (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))) n
        ≫ HomologicalComplex.homologyMap
            (Work.Cohomology.cokerInclSubIso (bigA_sub_bigB n W y r)).hom n) := by
      rw [← hh]; exact h1
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap
        (cokernel.map (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bdrySetW n W)
            (bdryMinus_sub_bdrySetW n W y))
          (Work.Cohomology.inclChainsSub W (bigA n W y r) (bigB n W y r) (bigA_sub_bigB n W y r))
          (Work.Cohomology.inclChainsSub W (bdryMinus n W y) (bigA n W y r)
            (bdryMinus_sub_bigA n W y r))
          (Work.Cohomology.inclChainsSub W (bdrySetW n W) (bigB n W y r)
            (bdrySetW_sub_bigB n W y r))
          (Work.Orient.Boundary.tripleCompat (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
            (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r))) n)
      (HomologicalComplex.homologyMap
        (Work.Cohomology.cokerInclSubIso (bigA_sub_bigB n W y r)).hom n)
  haveI : IsIso (HomologicalComplex.homologyMap
      (tripleMap W (bdryMinus_sub_bdrySetW n W y) (bigA_sub_bigB n W y r)
        (bdryMinus_sub_bigA n W y r) (bdrySetW_sub_bigB n W y r)).τ₁ n) := hIso
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end Work.Orient.Boundary
