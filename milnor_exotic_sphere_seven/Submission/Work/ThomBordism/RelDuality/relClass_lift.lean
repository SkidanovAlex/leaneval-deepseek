import Mathlib
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.ThomBordism.RelDuality.CollapseData
import Submission.Work.ThomBordism.RelDuality.collapsePiece
import Submission.Work.ThomBordism.RelDuality.relClass_lift_of_boundaryCollapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `relClass_lift`: every relative class of `H^k(M, ∂M)` is supported off the boundary

This file proves `Work.ThomBordism.RelDuality.relClass_lift`: for a compact charted
`9`-manifold with boundary `M` and every class `u` of `H^k(M, ∂M; ℤ)` there is a compact
`K ⊆ int M` such that `u` is the image of a class of `H^k(M, Kᶜ; ℤ)` under the restriction
`relRestrOffBdry`.  This is the "compactly supported cohomology of the interior computes the
relative cohomology" half of Hatcher's Theorem 3.43.

## Strategy

`RelDuality.relClass_lift_of_boundaryCollapse` already deduces the statement from a single
geometric input, `RelDuality.BoundaryCollapse M`: a compact `K ⊆ int M` together with a self-map
`ψ` of `M` that sends `Kᶜ` into `∂M`, fixes `∂M`, and is homotopic to the identity through maps
keeping `∂M` inside itself.  So it suffices to produce that datum, and this is done here from the
*chart-wise collapse pieces* of `Submission/Work/ThomBordism/RelDuality/collapsePiece.lean` (this is
the alternative to the collar neighbourhood theorem: it uses only charts).

Recall from that file:

* `ColDatum M` — a chart `e` of the atlas, an ambient centre `c`, a core radius `r` and an outer
  radius `R > r`; `ColDatum.ofPoint M x` is the datum at `x` (centre `(chartAt x) x`, `r = R/2`),
  `D.region`/`D.core` are the preimages of the ambient `R`-ball/`r`-ball, and `D.localMap hctr t`
  is the map of the piece at time `t`: the chart conjugate of the model scaling which *fixes the
  boundary hyperplane pointwise* and is the identity off `D.region`;
* `ColDatum.localMap_mem_boundary_of_mem_core` — at time `1` the piece sends `D.core` into `∂M`;
* `ColDatum.ofPoint_mem_interior_core` — every boundary point lies in the interior of the core of
  its own datum, so `∂M` is covered by the interiors of finitely many cores (compactness).

**Gluing the pieces.** Write `ψ_y` for the piece at a boundary point `y`.  Since `∂M` is fixed
pointwise by every piece at every time, `∂M` is a *stable* set for the composition, and the right
composite to collapse `Kᶜ` onto `∂M` is the iterated one: for a list `L = [y₁,…,yₙ]` put

`colComp L (x,t) = ψ_{yₙ} (t, … ψ_{y₂} (t, ψ_{y₁} (t, x)) …)`

and define `colGood` by

`colGood [] = ∅`,   `colGood (y :: L) = int (core y) ∪ ψ_y (1,·)⁻¹ (colGood L)`,

i.e. the set of points which, at some stage of the iteration, lie in the interior of the core of the
piece which is applied at that stage (and hence are sent to `∂M` by it).  Then

* `colGood L` is open (preimages of open sets) and contains `∂M ∩ ⋃_{y ∈ L} int core y`, so
  `K := (colGood L)ᶜ` is compact and lies in `int M`;
* `colComp L (·,1)` maps `colGood L` into `∂M`: once an iterate lands in a core, that piece sends
  it to `∂M`, and all later pieces fix `∂M` pointwise;
* `colComp L (·,t)` fixes `∂M` pointwise at every `t`, and `colComp L (·,0) = id`.

The definition by pullbacks is what makes this work without any estimate on the overlap of the
chart pieces: the set `K` is *defined* as the complement of the pullback union.

## Main statements

* `Work.ThomBordism.RelDuality.exists_boundaryCollapse` — a compact charted `9`-manifold with
  boundary admits the boundary collapse datum (no collar needed);
* `Work.ThomBordism.RelDuality.relClass_lift` — the delegated statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology unitInterval
open Function Set

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M]

/-! ## The collapse pieces at boundary points -/

/-- The *piece datum* at a boundary point: the chart-wise collapse piece of
`RelDuality.collapsePiece` centred at the point, whose centre lies on the boundary hyperplane of
its chart. -/
def bdryDatum (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    ColDatum M :=
  ColDatum.ofPoint M y.1

theorem bdryDatum_center_zero (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    (bdryDatum y).center 0 = 0 :=
  ColDatum.ofPoint_center_zero y.1 y.2

/-- The map of the collapse piece at the boundary point `y`, at time `t`. -/
def bdryMap (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) (t : ℝ)
    (x : M) : M :=
  (bdryDatum y).localMap (bdryDatum_center_zero y) t x

theorem continuous_bdryMap (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    Continuous fun p : M × ℝ => bdryMap y p.2 p.1 :=
  (bdryDatum y).continuous_localMap_uncurry (bdryDatum_center_zero y)

/-- The piece at a boundary point is continuous at time `1`. -/
theorem continuous_bdryMap_one
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    Continuous (fun x : M => bdryMap y 1 x) :=
  (continuous_bdryMap y).comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : M => (1 : ℝ)))

theorem bdryMap_zero (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M})
    (x : M) : bdryMap y 0 x = x :=
  (bdryDatum y).localMap_zero (bdryDatum_center_zero y) x

theorem bdryMap_eq_self_of_mem_boundary
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) {x : M}
    (hxb : x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M) (t : ℝ) :
    bdryMap y t x = x :=
  (bdryDatum y).localMap_eq_self_of_mem_boundary (bdryDatum_center_zero y) hxb t

/-- **A piece collapses its core onto the boundary** at time `1`. -/
theorem bdryMap_mem_boundary_of_mem_core
    (y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) {x : M}
    (hx : x ∈ (bdryDatum y).core) :
    bdryMap y 1 x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M :=
  (bdryDatum y).localMap_mem_boundary_of_mem_core (bdryDatum_center_zero y) hx

/-! ## The iterated collapse of a list of pieces -/

/-- **The iterated collapse map** of a list of pieces: `colComp [y₁,…,yₙ] (x,t)` applies the piece
at `y₁` first and the piece at `yₙ` last, all at time `t`. -/
def colComp :
    List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M} → M × ℝ → M
  | [] => fun p => p.1
  | y :: L => fun p => colComp L (bdryMap y p.2 p.1, p.2)

/-- **The collapsed set** of a list of pieces: the points which, at some stage of the iteration, are
in the interior of the core of the piece applied at that stage.  The collapse `colComp L (·,1)` maps
this set into `∂M`; its complement is the compact `K` of the boundary collapse datum. -/
def colGood :
    List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M} → Set M
  | [] => ∅
  | y :: L => interior (bdryDatum y).core ∪ bdryMap y 1 ⁻¹' (colGood L)

theorem continuous_colComp
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    Continuous (colComp L) := by
  induction L with
  | nil => exact continuous_fst
  | cons y L ih =>
    exact ih.comp ((continuous_bdryMap y).prodMk continuous_snd)

theorem colComp_zero
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    ∀ x : M, colComp L (x, 0) = x := by
  induction L with
  | nil => intro x; rfl
  | cons y L ih =>
    intro x
    show colComp L (bdryMap y 0 x, 0) = x
    rw [bdryMap_zero y x, ih x]

/-- **The iterated collapse fixes `∂M` pointwise at every time.** -/
theorem colComp_eq_self_of_mem_boundary
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      ∀ t : ℝ, colComp L (x, t) = x := by
  induction L with
  | nil => intro x _ t; rfl
  | cons y L ih =>
    intro x hxb t
    show colComp L (bdryMap y t x, t) = x
    rw [bdryMap_eq_self_of_mem_boundary y hxb t, ih x hxb t]

theorem isOpen_colGood
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    IsOpen (colGood L) := by
  induction L with
  | nil => exact isOpen_empty
  | cons y L ih =>
    exact isOpen_interior.union (ih.preimage (continuous_bdryMap_one y))

/-- **The key property of the iterated collapse**: at time `1` it maps the collapsed set into the
boundary. -/
theorem colComp_mem_boundary_of_mem_colGood
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    ∀ x : M, x ∈ colGood L →
      colComp L (x, 1) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M := by
  induction L with
  | nil => intro x hx; exact absurd hx (by simp [colGood])
  | cons y L ih =>
    intro x hx
    rcases hx with hx | hx
    · have hcore : x ∈ (bdryDatum y).core := interior_subset hx
      have hb : bdryMap y 1 x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M :=
        bdryMap_mem_boundary_of_mem_core y hcore
      show colComp L (bdryMap y 1 x, 1) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
      rw [colComp_eq_self_of_mem_boundary L (bdryMap y 1 x) hb 1]
      exact hb
    · exact ih (bdryMap y 1 x) hx

/-- **Every boundary point inside the union of the cores is collapsed**: the iterated collapse
sends the boundary points which lie in the interior of a core of one of its pieces into `∂M`. -/
theorem mem_colGood_of_mem_boundary_core
    (L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M}) :
    ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      (∃ y ∈ L, x ∈ interior (bdryDatum y).core) → x ∈ colGood L := by
  induction L with
  | nil => intro x _ hx; exact absurd hx (by simp)
  | cons a L ih =>
    intro x hxb hx
    rcases hx with ⟨z, hz, hxz⟩
    rcases List.mem_cons.mp hz with hza | hzL
    · rw [hza] at hxz
      exact Or.inl hxz
    · refine Or.inr ?_
      show bdryMap a 1 x ∈ colGood L
      rw [bdryMap_eq_self_of_mem_boundary a hxb 1]
      exact ih x hxb ⟨z, hzL, hxz⟩

/-! ## The boundary collapse datum -/

/-- **A compact charted `9`-manifold with boundary admits the boundary collapse datum** of
`RelDuality.CollapseData`, built from finitely many chart-wise collapse pieces and *without* using a
collar. -/
theorem exists_boundaryCollapse : Nonempty (BoundaryCollapse M) := by
  classical
  have hbdry_closed : IsClosed ((modelWithCornersEuclideanHalfSpace 9).boundary M) :=
    (modelWithCornersEuclideanHalfSpace 9).isClosed_boundary (n := (1 : WithTop ℕ∞))
      (by norm_num)
  obtain ⟨S, hS⟩ := hbdry_closed.isCompact.elim_finite_subcover
    (fun y : {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M} =>
      interior (bdryDatum y).core)
    (fun _ => isOpen_interior)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ColDatum.ofPoint_mem_interior_core x hx⟩)
  let L : List {x : M // x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M} := S.toList
  have hL : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      ∃ y ∈ L, x ∈ interior (bdryDatum y).core := by
    intro x hx
    have h := hS hx
    rw [Set.mem_iUnion] at h
    obtain ⟨y, h⟩ := h
    rw [Set.mem_iUnion] at h
    obtain ⟨hy, hxy⟩ := h
    exact ⟨y, by simpa [L] using hy, hxy⟩
  have hgood : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      x ∈ colGood L :=
    fun x hx => mem_colGood_of_mem_boundary_core L x hx (hL x hx)
  refine ⟨{ K := (colGood L)ᶜ
            hK := fun x hx hxb => hx (hgood x hxb)
            hKc := (isOpen_colGood L).isClosed_compl.isCompact
            ψ := ⟨fun x => colComp L (x, 1),
              (continuous_colComp L).comp (Continuous.prodMk continuous_id continuous_const)⟩
            ψ_compl := fun x hx => colComp_mem_boundary_of_mem_colGood L x (by simpa using hx)
            ψ_bdry := fun x hxb => by
              show colComp L (x, 1) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
              rw [colComp_eq_self_of_mem_boundary L x hxb 1]
              exact hxb
            ψ_fix := fun x hxb => by
              show colComp L (x, 1) = x
              exact colComp_eq_self_of_mem_boundary L x hxb 1
            H := ContinuousMap.Homotopy.mk
              ⟨fun q : unitInterval × M => colComp L (q.2, (q.1 : ℝ)),
                (continuous_colComp L).comp (Continuous.prodMk continuous_snd
                  (continuous_subtype_val.comp continuous_fst))⟩
              (fun x => colComp_zero L x) (fun x => rfl)
            H_bdry := fun t x hxb => by
              show colComp L (x, (t : ℝ)) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
              rw [colComp_eq_self_of_mem_boundary L x hxb (t : ℝ)]
              exact hxb }⟩

/-- **`relClass_lift`.**  Every class of `H^k(M, ∂M; ℤ)` restricts from the cohomology of a
neighbourhood of a compact subset of the interior. -/
theorem relClass_lift {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
    (k : ℕ) :
    ∀ u : (Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((modelWithCornersEuclideanHalfSpace 9).boundary M)).homology k,
      ∃ (K : Set M) (hK : K ⊆ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}),
        IsCompact K ∧
        ∃ x : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k,
          (HomologicalComplex.homologyMap
            (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) x = u := by
  intro u
  obtain ⟨C⟩ := exists_boundaryCollapse (M := M)
  exact relClass_lift_of_boundaryCollapse (M := M) C k u

end

end Work.ThomBordism.RelDuality
