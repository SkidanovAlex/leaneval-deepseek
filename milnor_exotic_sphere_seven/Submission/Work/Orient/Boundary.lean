import Mathlib
import Submission.Work.Orient.Defs
import Submission.Work.Orient.Closed
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# ORIENT: fundamental classes of compact manifolds with boundary (item 2)

This file fixes the **vocabulary**, the **exact statements** and the **interface to the missing
chapter** for relative fundamental classes of compact manifolds with boundary (Mathlib's `𝓡∂`
half-space model).

## The vocabulary

* `Work.Orient.halfIncl` — the half-space model `𝓡∂ n` as a map into the ambient
  `EuclideanSpace ℝ (Fin n)` (a closed embedding).  It is through this map that metric statements
  about the half-space are made, because `EuclideanHalfSpace n` carries no `PseudoMetricSpace`.
* `Work.Orient.halfBallPiece` — the coordinate piece `K(z,r)` of `𝓡∂ n` centred at `z`: the chart
  preimage of the closed ball of radius `r/2` around the image of `z`, measured in the ambient space.
  At a **boundary point** this is a genuine half-ball; at an interior point it is an ordinary
  coordinate ball.  (Defining the piece as the chart preimage of a Euclidean ball *alone* would be
  wrong: around a boundary point such a ball leaves the half-space.)
* `Work.Orient.IsCoordHalfBall` — `K = halfBallPiece n W z r` for some `z, r` (with the standard
  "ball inside the chart target" side condition).
* `Work.Orient.IsHalfOrientationFamily` — an **orientation of a manifold with boundary**: a family of
  local generators at the *interior* points, coherent over coordinate half-balls.
* `Work.Orient.IsRelFundClass` (in `Defs.lean`) — a relative fundamental class: `w ∈ H_{n+1}(W,B)`
  restricts to a local generator at every point outside `B`; for `B = ∂W` this is the local-generator
  property at every interior point, which is exactly the field `Work.ThomBordism.NullBordismFamily.w_fund`.
* `Work.Orient.BoundaryOrientationConvention` — the **boundary-orientation convention**: the
  connecting map `hPairδ` of the pair `(W, ∂W)` sends a relative fundamental class to a fundamental
  class of `∂W`; that class is, by definition, the class of the induced boundary orientation.  It is
  the `+`-sign convention (the other one would give `-hPairδ w`), and it is the convention used by
  `Work.ThomBordism.NullBordismFamily.hw`.
* `Work.Orient.RelativeFundamentalClassExists` — **existence** of the relative fundamental class
  from a half-orientation, together with the boundary formula.

## Status, and the missing chapter

`RelativeFundamentalClassExists` and `BoundaryOrientationConvention` are **named inputs**: they are
Propositions (not axioms), and every statement of this chapter that needs them records the dependency
once.  Proving them is the half-space port of Hatcher 3.27/3.43, whose Euclidean version is the
chapter `Submission/Work/Orient/Closed.lean` (with its machinery in
`Submission/Work/Orient/Port/Hatcher.lean`, `Port/Hatcher2.lean`, `Work.ThomBordism.convexCover`).

The missing chapter is stated here as the four `Prop`s below, bundled in
`Work.Orient.HalfSpaceHatcher`; each is a precise, self-contained statement about the half-space
model, with no orientation theory in it:

* `Work.Orient.HalfVanishingProp` — Hatcher 3.27(a) for the half-space model: `H_i(W, W∖A) = 0` for
  `i > n+1` and `A` compact;
* `Work.Orient.HalfCoverProp` — a compact set is covered by finitely many coordinate half-balls
  centred at its points and avoiding a disjoint closed set (the half-space analogue of
  `Work.ThomBordism.exists_ball_cover_avoiding`);
* `Work.Orient.HalfRestrictIsoProp` — the restriction `H_{n+1}(W, W∖K(z,r)) → H_{n+1}(W, W∖{z})` out
  of a coordinate half-ball is an isomorphism (the half-space analogue of
  `Work.ThomBordism.convexLocalIso`);
* `Work.Orient.HalfLocalHomologyProp` — the local group `H_{n+1}(W, W∖{x})` is `ℤ` at an interior
  point and `0` at a boundary point.

`Work.Orient.RelativeFundamentalClassExists` is the orientation-theoretic consequence.  The reductions
proved in this directory and their exact form are documented in `README.md`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient

noncomputable section

variable {N : ℕ}

/-! ## Coordinate half-balls -/

/-- The **half-space model space** as a function into the ambient `EuclideanSpace ℝ (Fin n)`.
`EuclideanHalfSpace n` carries no `PseudoMetricSpace` of its own, so all metric statements about the
half-space model are made in the ambient space through this map, which is a closed embedding
(`ModelWithCorners.isClosedEmbedding`). -/
abbrev halfIncl (n : ℕ) [NeZero n] : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n) :=
  fun y => modelWithCornersEuclideanHalfSpace n y

/-- The **coordinate half-ball piece** of a space charted in the half-space model `𝓡∂ n`, with
centre `z` and radius `r`: the chart preimage of the closed ball of radius `r/2` around the image of
`z`, **measured in the ambient space** through `Work.Orient.halfIncl`.

Cutting back to the half-space is essential at a **boundary point** of a manifold with boundary: a
Euclidean ball around a boundary point leaves the half-space, whereas at an interior point the piece
is an ordinary coordinate ball. -/
def halfBallPiece (n : ℕ) [NeZero n] (W : TopCat) [ChartedSpace (EuclideanHalfSpace n) W]
    (z : W) (r : ℝ) : Set W :=
  (chartAt (EuclideanHalfSpace n) z) ⁻¹'
      (halfIncl n ⁻¹' Metric.closedBall
        (halfIncl n ((chartAt (EuclideanHalfSpace n) z) z)) (r / 2)) ∩
    (chartAt (EuclideanHalfSpace n) z).source

/-- The side condition of a coordinate half-ball: the open ball of radius `r` around the image of
`z` lies inside the chart target. -/
def halfBallGood (n : ℕ) [NeZero n] (W : TopCat) [ChartedSpace (EuclideanHalfSpace n) W]
    (z : W) (r : ℝ) : Prop :=
  halfIncl n ⁻¹' Metric.ball (halfIncl n ((chartAt (EuclideanHalfSpace n) z) z)) r ⊆
    (chartAt (EuclideanHalfSpace n) z).target

/-- A **coordinate half-ball** of a space charted in the half-space model `𝓡∂ n`. -/
def IsCoordHalfBall (n : ℕ) [NeZero n] (W : TopCat) [ChartedSpace (EuclideanHalfSpace n) W]
    (K : Set W) : Prop :=
  ∃ z : W, ∃ r : ℝ, 0 < r ∧ halfBallGood n W z r ∧ K = halfBallPiece n W z r

/-- The centre of a coordinate half-ball lies in it. -/
theorem mem_halfBallPiece_center {n : ℕ} [NeZero n] {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace n) W] {z : W} {r : ℝ} (hr : 0 < r) :
    z ∈ halfBallPiece n W z r := by
  refine ⟨?_, mem_chart_source _ z⟩
  show halfIncl n ((chartAt (EuclideanHalfSpace n) z) z) ∈
    Metric.closedBall (halfIncl n ((chartAt (EuclideanHalfSpace n) z) z)) (r / 2)
  rw [Metric.mem_closedBall, dist_self]
  linarith

/-- The coordinate half-ball piece is compact (under the standard side condition). -/
theorem halfBallPiece_isCompact {n : ℕ} [NeZero n] {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace n) W] (z : W) (r : ℝ) (hr : 0 < r)
    (hball : halfBallGood n W z r) : IsCompact (halfBallPiece n W z r) := by
  set e := chartAt (EuclideanHalfSpace n) z with he
  set I := modelWithCornersEuclideanHalfSpace n with hI
  have hsub : halfIncl n ⁻¹' Metric.closedBall (halfIncl n (e z)) (r / 2) ⊆ e.target :=
    fun y hy => hball ((Metric.closedBall_subset_ball (by linarith)) hy)
  have hcpt : IsCompact (halfIncl n ⁻¹' Metric.closedBall (halfIncl n (e z)) (r / 2)) :=
    I.isClosedEmbedding.isInducing.isCompact_preimage I.isClosedEmbedding.isClosed_range
      (isCompact_closedBall _ _)
  have heq : e ⁻¹' (halfIncl n ⁻¹' Metric.closedBall (halfIncl n (e z)) (r / 2)) ∩ e.source
      = e.symm '' (halfIncl n ⁻¹' Metric.closedBall (halfIncl n (e z)) (r / 2)) := by
    rw [Set.inter_comm, OpenPartialHomeomorph.symm_image_eq_source_inter_preimage e hsub]
  rw [halfBallPiece, ← he, heq]
  exact hcpt.image_of_continuousOn (e.continuousOn_symm.mono hsub)

/-- A coordinate half-ball is compact. -/
theorem IsCoordHalfBall.isCompact {n : ℕ} [NeZero n] {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace n) W] {K : Set W} (h : IsCoordHalfBall n W K) :
    IsCompact K := by
  obtain ⟨z, r, hr, hball, rfl⟩ := h
  exact halfBallPiece_isCompact z r hr hball

/-- A coordinate half-ball is closed. -/
theorem IsCoordHalfBall.isClosed {n : ℕ} [NeZero n] {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace n) W] {K : Set W} (h : IsCoordHalfBall n W K) :
    IsClosed K :=
  h.isCompact.isClosed

/-! ## Orientations of a manifold with boundary -/

/-- **An orientation of a manifold with boundary**, as a locally consistent family of local
generators at the interior points.

`γ x` generates `H_{n+1}(W, W∖{x})` (a `ℤ`, see
`Work.Orient.Boundary.localHomology_corner`) for every interior point `x`, and for every coordinate
half-ball `K` **disjoint from `∂W`** the classes `γ x`, `x ∈ K`, are the specialisations of one class
of `H_{n+1}(W, W∖K)`.

The disjointness from `∂W` is essential and not a convenience.  For a coordinate piece `K` centred at
a **boundary point**, the relative group `H_{n+1}(W, W∖K)` **vanishes**: by excision it is
`H_{n+1}(U, U∖K)` for the open half-ball `U` containing `K`, and both `U` and `U∖K` (a half-annulus,
which retracts onto its outer half-sphere) are contractible, so the long exact sequence of the pair
gives `0` — and by `Work.Orient.Boundary.localHomology_corner` the local group at every boundary
point is `0` as well.  Hence the only class over such a piece is `0`, and demanding that it
specialise to a *generator* at the interior points of `K` would be unsatisfiable and would make the
notion empty.  In other words the local generator data of an orientation lives over the pieces
**contained in the interior** — which is exactly what an oriented atlas supplies (the transition
functions of a chart cover of the interior have positive Jacobian determinants). -/
def IsHalfOrientationFamily (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      LocH W (n + 1) x) : Prop :=
  (∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
      Submodule.span ℤ ({γ x hx} : Set (LocH W (n + 1) x)) = ⊤) ∧
    ∀ K : Set W, IsCoordHalfBall (n + 1) W K →
      (∀ x ∈ K, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) →
      ∃ a : RelH W (n + 1) K,
        ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          (hxK : x ∈ K),
          resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxK) a = γ x hx

/-- **Orientation reversal** of a half-orientation family. -/
theorem IsHalfOrientationFamily.neg {n : ℕ} {W : TopCat}
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      LocH W (n + 1) x} (h : IsHalfOrientationFamily n W γ) :
    IsHalfOrientationFamily n W (fun x hx => - γ x hx) := by
  refine ⟨fun x hx => ?_, fun K hK hKb => ?_⟩
  · have hs : ({-γ x hx} : Set (LocH W (n + 1) x)) = -({γ x hx} : Set (LocH W (n + 1) x)) := by
      ext y; simp
    rw [hs, Submodule.span_neg]
    exact h.1 x hx
  · obtain ⟨a, ha⟩ := h.2 K hK hKb
    refine ⟨-a, fun x hx hxK => ?_⟩
    rw [map_neg, ha x hx hxK]
    try rfl

/-! ## The boundary-orientation convention -/

/-- **The boundary-orientation convention.**  The connecting homomorphism
`hPairδ : H_{n+1}(W, ∂W) → H_n(∂W)` of the long exact sequence of the pair sends a relative
fundamental class to a fundamental class of the boundary; *that* class is, by definition, the class
of the **induced boundary orientation**.  (With the opposite convention one would get
`hPairδ w = -[∂W]`.)  This is the convention used by `Work.ThomBordism.NullBordismFamily.hw`.

The statement as written is deliberately **sign-blind** (`IsFundClass` is invariant under
`c ↦ -c`): it says that `hPairδ w` generates the local groups of `∂W`, which is the mathematical
content of "`hPairδ [W,∂W]` is the class of the boundary orientation".  A *signed* form (an
equality in `H_n(∂W)`, as in the consumer's `hw`) additionally requires fixing the orientation
conventions of the ambient and of the boundary — the `outward normal first` convention of the
docstring above — and is not part of this `Prop`. -/
def BoundaryOrientationConvention : Prop :=
  ∀ (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (w : (Work.Cohomology.relChains W
      ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1)),
    IsRelFundClass W (n + 1) ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w →
      IsFundClass (TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        (Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n w)

/-! ## The missing chapter: the half-space port of Hatcher 3.27 -/

/-- **Hatcher 3.27(a) for the half-space model**: for a space charted in dimension `n+1` by the
half-space, a compact subset `A` and `i > n+1`, the relative homology `H_i(W, W∖A)` vanishes.  (The
Euclidean version is `Work.Cohomology.relChains_vanishing_of_compact`.) -/
def HalfVanishingProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (A : Set W),
    IsCompact A → ∀ i : ℕ, n + 1 < i → CategoryTheory.Limits.IsZero (RelH W i A)

/-- **A compact set is covered by finitely many coordinate half-balls centred at its points,
avoiding a disjoint closed set** — the half-space analogue of
`Work.Orient.Port.exists_ball_cover_avoiding` (`Work.ThomBordism.exists_ball_cover_avoiding`). -/
def HalfCoverProp (n : ℕ) : Prop :=
  ∀ (W : TopCat.{0}) [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {A S : Set W},
    IsCompact A → Disjoint A S → IsClosed S →
      ∃ (m : ℕ) (z : Fin m → W) (r : Fin m → ℝ),
        (∀ i, 0 < r i) ∧ (∀ i, halfBallGood (n + 1) W (z i) (r i)) ∧
        (∀ i, z i ∈ A) ∧
        A ⊆ ⋃ i, halfBallPiece (n + 1) W (z i) (r i) ∧
        Disjoint S (⋃ i, halfBallPiece (n + 1) W (z i) (r i))

/-- **The restriction out of a coordinate half-ball at its centre is an isomorphism** — the
half-space analogue of `Work.ThomBordism.convexLocalIso`.

The side condition is **not** a convenience: `K` has to lie in the *interior* of `W`.  Without it
the statement is **false**, and the machine-checked refutation is
`Work.Orient.Boundary.Counterexample.halfRestrictIso_false_zero`
(`Submission/Work/Orient/Boundary/HalfRestrictIsoCounterexample.lean`): for the closed interval
`[-1,1]` with a two-chart half-space structure, `z = 0` (an interior point) and `r = 3`, the closed
ball of radius `r/2` around the chart image of `z` reaches the hyperplane of the model, the piece
`K` becomes a ball *plus* a piece of the boundary layer, and `H_{n+1}(W, W∖K) = 0` while
`H_{n+1}(W, W∖{z}) ≅ ℤ`.  When `K` lies in the interior, the model is locally Euclidean along `K`,
the radial retraction from `z` stays inside it, and the proof of `convexLocalIso` ports verbatim; at
a *boundary* centre both groups vanish (`Work.Orient.Boundary.localHomology_corner`). -/
def HalfRestrictIsoProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (z : W) (r : ℝ) (hr : 0 < r) (hball : halfBallGood (n + 1) W z r),
    (∀ x ∈ halfBallPiece (n + 1) W z r,
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) →
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
      (halfBallPiece (n + 1) W z r)ᶜ ({z} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
        (mem_halfBallPiece_center hr)))) (n + 1))

/-- The **refuted** form of `HalfRestrictIsoProp`, without the interior side condition: it holds for
every compact charted `W`, every `z` and every `r`.  It is **false** — see
`Work.Orient.Boundary.Counterexample.halfRestrictIso_false_zero` — and is kept here only as the
record of the statement that the counterexample refutes. -/
def HalfRestrictIsoNoSideConditionProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (z : W) (r : ℝ) (hr : 0 < r) (hball : halfBallGood (n + 1) W z r),
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W
      (halfBallPiece (n + 1) W z r)ᶜ ({z} : Set W)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr
        (mem_halfBallPiece_center hr)))) (n + 1))

/-- **The local homology of a manifold with boundary**: `H_{n+1}(W, W∖{x}) ≅ ℤ` at an interior
point and `0` at a boundary point. -/
def HalfLocalHomologyProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (x : W),
    (x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        Nonempty (LocH W (n + 1) x ≅ ModuleCat.of ℤ ℤ)) ∧
      (x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
        CategoryTheory.Limits.IsZero (LocH W (n + 1) x))

/-- The local input of the half-space port is **proved** (in
`Submission/Work/Orient/Boundary/localHomology_corner.lean`), so this component of
`HalfSpaceHatcher` is no longer an input. -/
theorem halfLocalHomologyProp (n : ℕ) : HalfLocalHomologyProp n :=
  fun W _ _ x => Work.Orient.Boundary.localHomology_corner n W x

/-- **At a boundary point the local group is a subsingleton** (so any two local classes at a
boundary point are automatically equal) — the form in which the triviality of the local group is
used in gluing arguments. -/
theorem subsingleton_locH_of_mem_boundary {n : ℕ} (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {x : W}
    (hx : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    Subsingleton (LocH W (n + 1) x) :=
  ModuleCat.subsingleton_of_isZero ((halfLocalHomologyProp n W x).2 hx)

/-- **Uniqueness over a compact set of the interior** — the half-space analogue of
`Work.Orient.Port.compactZero`: a class of `H_{n+1}(W, W∖A)`, `A` a compact subset of the
**interior**, whose localisation at every point of `A` vanishes is zero.

The interior hypothesis is essential: for `A = ∂W` the localisation at every point of `A` is
automatically zero (the local groups vanish, `Work.Orient.subsingleton_locH_of_mem_boundary`) while
`H_{n+1}(W, ∂W)` need not vanish (it is `ℤ` for a connected oriented `W`).  All the sets to which
this is applied in the gluing are contained in the interior anyway. -/
def HalfCompactZeroProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {A : Set W}, IsCompact A →
      (∀ x ∈ A, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) →
      ∀ β : RelH W (n + 1) A,
      (∀ (x : W) (hx : x ∈ A),
        resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) β = 0) → β = 0

/-- **Gluing over a finite cover by coordinate half-balls** — the half-space analogue of
`Work.Orient.Port.coverGlue`: classes over the pieces which agree at every point of the pairwise
intersections are the restrictions of one class over the union. -/
def HalfCoverGlueProp (n : ℕ) : Prop :=
  ∀ (W : TopCat.{0}) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {m : ℕ} (K : Fin m → Set W), (∀ i, IsCoordHalfBall (n + 1) W (K i)) →
      (∀ (i : Fin m) (x : W), x ∈ K i → x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) →
      ∀ ζ : ∀ i, RelH W (n + 1) (K i),
      (∀ (i j : Fin m) (x : W) (hx : x ∈ K i ∩ K j),
        resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.1) (ζ i)
          = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.2) (ζ j)) →
      ∃ γ : RelH W (n + 1) (⋃ i, K i), ∀ i,
        resRelH W (n + 1) (Set.subset_iUnion K i) γ = ζ i

/-- **The missing chapter of the ORIENT area**: the half-space port of Hatcher 3.27, i.e. of
`Submission/Work/Orient/Port/Hatcher.lean` + `Port/Hatcher2.lean` + `Work.ThomBordism.convexLocalIso`
+ `Work.ThomBordism.convexCover`, from the Euclidean model to the half-space model `𝓡∂`.

The fourth component `HalfLocalHomologyProp` is *proved*, see `halfLocalHomologyProp`; it is kept out
of the bundle so that what remains is exactly the port that is still missing. -/
def HalfSpaceHatcher (n : ℕ) : Prop :=
  HalfVanishingProp n ∧ HalfCoverProp n ∧ HalfRestrictIsoProp n

/-! ## The geometric residue: the core-to-boundary transfer -/

/-- The **too strong form** of `CoreIsoProp`, with the condition imposed on *every* compact
`C ⊇ C₀`: it is **FALSE**.  Take `W = [0,1]`, `n = 0`, `C₀ = [a,b] ⊆ (0,1)` and
`C = [a,b] ∪ [c,d]` with `a < c < d < b`: then `C` is compact, `C₀ ⊆ C ⊆ W°`, but
`W∖C = [0,a) ∪ (c,d) ∪ (b,1]` has three components against the two of `∂W`, so
`H_1(W,∂W) ≅ ℤ` while `H_1(W, W∖C) ≅ ℤ²` and the map is not an isomorphism.  It is kept here only
as the record of the statement that the review of `Orient/Boundary/CoreIsoOfCollar` refuted (and of
the hypothesis of `Work.Orient.Boundary.RelFundClassOfCoreIso`, which is therefore vacuous). -/
def CoreIsoAllCoresProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W],
    ∃ (C₀ : Set W), IsCompact C₀ ∧
      (∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ∧
      ∀ (C : Set W), IsCompact C → C₀ ⊆ C →
        (hCint : ∀ x ∈ C, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) →
        IsIso (HomologicalComplex.homologyMap (relChainsIncl W
          (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := Cᶜ)
          (fun y hy hyc => hCint y hyc hy)) (n + 1))

/-- **The geometric input of item 2** (the homological shadow of the collar theorem): there is a
compact *core* `C₀` of the interior, meeting every path-component of the interior, such that the
restriction of pairs

`H_{n+1}(W, ∂W) ⟶ H_{n+1}(W, W∖C₀)`

is an isomorphism.  With a collar `c : ∂W × [0,∞) ↪ W` one takes `C₀ = W ∖ c(∂W × [0,ε))`: then
`W∖C₀ = c(∂W × [0,ε))` deformation retracts onto `∂W` **inside itself** (the straight-line homotopy
`(p,t) ↦ (p,(1-s)t)`), so the inclusion `∂W ↪ W∖C₀` is a homotopy equivalence and the five lemma for
pairs (`Work.Cohomology.relChainsMapOf_homologyMap_isIso`) gives the isomorphism.

The connectivity clause `hconn` is a statement about the **interior** `W° = W ∖ ∂W` *as a space in its
own right*: every point of `W°` is joined to a point of `C₀` by a path that stays in `W°`.  This is
strictly stronger than asking for a path in the whole of `W`, and it is exactly what the transport of
the local generator property needs (`Work.Orient.Boundary.IsRelFundClassOfCore`): a path in `W` may
leave the interior and re-enter it, and the local classes of `w ∈ H_{n+1}(W,∂W)` are only defined at
points of `W°`.  For a collar `c` the chosen `C₀` satisfies it, because `c(∂W × (0,∞)) ⊆ W°`.

Note the condition is imposed on the *core alone* and not on larger compact sets: for
`H_{n+1}(W, ∂W) → H_{n+1}(W, W∖C)` with an arbitrary `C ⊇ C₀` it is **false**
(`Work.Orient.CoreIsoAllCoresProp`).  The workspace carries the collar itself as the named input
`Work.Surgery.HasCollar` / `Work.Surgery.SmoothCollar` of the Surgery area; getting from a collar to
this `Prop` is pure topology and is the one step of item 2 that is not this area's business. -/
def CoreIsoProp (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W],
    ∃ (C₀ : Set W) (hCp : IsCompact C₀)
      (hint : ∀ x ∈ C₀, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      (hconn : ∀ (x : W) (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
        ∃ (y : W) (hy : y ∈ C₀)
          (hy' : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W),
          Nonempty (Path (⟨x, hx⟩ : {z : W //
              z ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) ⟨y, hy'⟩)),
      IsIso (HomologicalComplex.homologyMap (relChainsIncl W
        (A := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) (B := C₀ᶜ)
        (fun y hy hyc => hint y hyc hy)) (n + 1))

/-! ## Existence of the relative fundamental class -/

/-- **Existence of the relative fundamental class** (ORIENT, item 2).  A compact `C^∞` manifold `W`
with boundary (modelled on the half-space) carrying an orientation has a relative fundamental class
`[W, ∂W] ∈ H_{n+1}(W, ∂W; ℤ)` which is a local generator at every interior point, and whose boundary
`hPairδ [W,∂W]` is the fundamental class of `∂W` with the induced orientation (the convention of
`Work.Orient.BoundaryOrientationConvention`).

Proving this (equivalently, proving it from `Work.Orient.HalfSpaceHatcher`) is the half-space port
described in the header and in `README.md`. -/
def RelativeFundamentalClassExists (n : ℕ) : Prop :=
  ∀ (W : TopCat) [CompactSpace W] [T2Space W] [Nonempty W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (γ : ∀ x : W, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W →
      LocH W (n + 1) x),
    IsHalfOrientationFamily n W γ →
      ∃ w : (Work.Cohomology.relChains W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1),
        IsRelFundClass W (n + 1) ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) w ∧
          IsFundClass (TopCat.of ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
            (Work.Cohomology.hPairδ W
              ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n w)

end

end Work.Orient
