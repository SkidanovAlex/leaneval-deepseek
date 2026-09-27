import Mathlib
import Submission.Work.PL.Defs

/-!
# Connell's cell-count reduction (`Work.Cells.Connell`): interfaces

This chapter proves Connell's step of the Newman/Connell proof of the generalized
topological Poincaré conjecture in dimensions `≥ 5` (Newman 1966, §16; blueprint `A8`):

* `Work.Cells.Connell.connell_step` (blueprint `C2`): if a compact `n`-manifold-like space
  `M` (`n ≥ 5`, local cube charts, `(n-1)`-connected) is a union of `k + 3` open `n`-cells
  and admits an engulfing theorem (`E0`), then it is a union of `k + 2` open `n`-cells.
* `Work.Cells.Connell.cellCover_succ` (`C3` glue): `CellCover n M k → CellCover n M (k+1)`.
* `Work.Cells.Connell.cellCover_two`: iteration down to `2` cells.
* `Work.Cells.Connell.two_cells_sphere` (`C4`): a two-cell cover of a compact `M` has a
  point whose complement is homeomorphic to `ℝⁿ` (via Brown's criterion form).

Everything that belongs to another area of the blueprint enters `connell_step` as a
*hypothesis*, bundled in the structure `Assumptions n`; see the docstrings of the fields.
The vocabulary (`PL.E`, `PL.Cx`, `PL.CubeChart`, `PL.CellCover`, `PL.DomDim`, `PL.ExtOverDisc`,
`PL.CSupp`, …) is frozen in `Submission/Work/PL/Defs.lean`.

## Conventions

* `ℝⁿ` is `PL.E n`, and `PL.openCube r`, `PL.closedCube r` are *sup-norm* cubes.
* A `PL.CubeChart n M` is an open embedding of the open unit cube into `M`; only its values
  on `PL.openCube 1` are meaningful, so every statement below that uses a chart restricts to
  `PL.openCube 1` (or to `PL.closedCube r` with `r < 1`), or records the value on the
  complement of `PL.openCube 1` explicitly.
* `PL.MeshLT K δ` bounds the *vertex* diameter of the faces of `K`; the lemma
  `Work.Cells.Connell.meshLT_dist_lt` bounds the diameter of the simplices themselves.
-/

open Set Metric

namespace Work.Cells.Connell

universe u

/-! ## Auxiliary vocabulary -/

/-- A family of `Thin` sets: compact subsets of the open unit cube with empty interior.
This is the form in which the "dimension `≤ d`" hypothesis of the engulfing theorem
(`PL.DomDim`) is consumed: a `d`-dimensional (`d + 1 ≤ n`) subset of a closed sub-cube is a
finite union of such sets. -/
def ThinFamily {n : ℕ} {ι : Type*} (F : ι → Set (PL.E n)) : Prop :=
  ∀ i, IsCompact (F i) ∧ F i ⊆ PL.openCube (n := n) 1 ∧ interior (F i) = ∅

/-! ## The statements owned by the other areas of the blueprint -/

/-- **`E0`** (Newman's engulfing theorem, blueprint `A9`): if `X` is a closed, locally
`p`-dimensional subset of a space with local cube charts whose complement in `V` is compact,
and `V` is a nonempty open `(p-1)`-connected set, then `X` can be engulfed into `V` by a
homeomorphism of the whole space with compact support. -/
def EngulfForm (n : ℕ) : Prop :=
  ∀ (p : ℕ) (Y : Type u) [MetricSpace Y], p + 3 ≤ n → PL.LocCube n Y →
    (∀ j, j ≤ p → PL.ExtOverDisc Y j) →
    ∀ (V : Set Y), IsOpen V → V.Nonempty → (∀ j, j + 1 ≤ p → PL.ExtOverDisc ↥V j) →
    ∀ (X : Set Y), IsClosed X → IsCompact (X \ V) →
      (∀ x ∈ X, ∃ ψ : PL.CubeChart n Y, x ∈ ψ.toFun '' PL.openCube (1 / 2) ∧
        ∃ Pd : Set (PL.E n), PL.DomDim Pd p ∧
          ∀ y ∈ PL.closedCube (1 : ℝ), ψ.toFun y ∈ X → y ∈ Pd) →
      ∃ h : Y ≃ₜ Y, PL.CSupp h univ ∧ X ⊆ h '' V

/-- **`A6` / `G7`** (Connell–Stallings stretch between the two dual skeleta of a cube
triangulation): the data and properties of the low (`p`-skeleton) and high (dual) parts of a
triangulation of a cube.

`Low P p` is the `p`-skeleton of `P` and `High P p` is the dual `(n-p-1)`-skeleton (union of
those faces of the barycentric subdivision of `P` all of whose vertices are barycentres of
faces of `P` with at least `p+2` vertices).  The fields record exactly what Connell's step
consumes. -/
structure SkeletonData (n : ℕ) where
  /-- the low (`p`-skeleton) part -/
  Low : PL.Cx n → ℕ → Set (PL.E n)
  /-- the high (dual skeleton) part -/
  High : PL.Cx n → ℕ → Set (PL.E n)
  /-- `Low` lies in the polyhedron -/
  low_sub : ∀ (P : PL.Cx n) (p : ℕ), Low P p ⊆ P.space
  /-- `High` lies in the polyhedron -/
  high_sub : ∀ (P : PL.Cx n) (p : ℕ), High P p ⊆ P.space
  /-- `Low` is closed (it is a finite union of simplices) -/
  low_closed : ∀ (P : PL.Cx n) (p : ℕ), IsClosed (Low P p)
  /-- `High` is closed -/
  high_closed : ∀ (P : PL.Cx n) (p : ℕ), IsClosed (High P p)
  /-- the `p`-skeleton is `p`-dimensional -/
  low_dom : ∀ (P : PL.Cx n) (p : ℕ), PL.DomDim (Low P p) p
  /-- the dual `(n-p-1)`-skeleton is `(n-p-1)`-dimensional -/
  high_dom : ∀ (P : PL.Cx n) (p : ℕ), PL.DomDim (High P p) ((n - p - 1 : ℕ) : ℤ)
  /-- `dual_stretch` (`G7`): if `Low P p ⊆ N₁` and `High P p ⊆ N₂` for open `N₁`, `N₂`, then a
  self-homeomorphism of `ℝⁿ`, the identity outside the open cube of size `β` and preserving
  every simplex of `P`, carries the cube of size `α` into `h '' N₁ ∪ N₂`. -/
  dual_stretch : ∀ (p : ℕ) (β α : ℝ), p < n → 0 < α → α < β → (P : PL.Cx n) →
    P.faces.Finite → P.space = PL.closedCube β → ∀ (N₁ N₂ : Set (PL.E n)),
    IsOpen N₁ → IsOpen N₂ → Low P p ⊆ N₁ → High P p ⊆ N₂ →
    ∃ h : PL.E n ≃ₜ PL.E n, (∀ x, x ∉ PL.openCube β → h x = x) ∧
      (∀ s ∈ P.faces, h '' PL.simp s = PL.simp s) ∧
      PL.closedCube α ⊆ h '' N₁ ∪ N₂

/-- **`A7` / `G8`**: the cube annulus `openCube 1 \ closedCube β` is `(n-2)`-connected. -/
def AnnulusForm (n : ℕ) : Prop :=
  ∀ (β : ℝ), 0 < β → β < 1 → ∀ j, j + 2 ≤ n →
    PL.ExtOverDisc ↥(PL.openCube (n := n) 1 \ PL.closedCube β) j

/-- **`A7` / `C1`**: the complement of a closed chart cube in a connected space is
`(n-3)`-connected. -/
def CubeMinusForm (n : ℕ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (c : PL.CubeChart n M) (β : ℝ), 0 < β → β < 1 →
    ∀ j, j + 3 ≤ n → PL.ExtOverDisc M j → PL.ExtOverDisc ↥((c.toFun '' PL.closedCube β)ᶜ) j

/-- **`A7` / `C0`**: a homeomorphism of an open subspace supported in a compact set extends by
the identity to a homeomorphism of the ambient space. -/
def ExtHomeoForm (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] (O : Set M), IsOpen O → (h : ↥O ≃ₜ ↥O) →
    ∀ C : Set ↥O, IsCompact C → (∀ x, x ∉ C → h x = x) →
    ∃ H : M ≃ₜ M, (∀ x : ↥O, H x = h x) ∧ ∀ x, x ∉ O → H x = x

/-- **`A7`**: `PL.LocCube` passes to open subspaces. -/
def LocCubeOpenForm (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] (O : Set M), IsOpen O → PL.LocCube n M → PL.LocCube n ↥O

/-- **`A2` / `G7`**: existence of a triangulation of the closed `β`-cube with mesh `< δ`. -/
def CubeTriangulationForm (n : ℕ) : Prop :=
  ∀ (β δ : ℝ), 0 < β → 0 < δ →
    ∃ P : PL.Cx n, P.faces.Finite ∧ P.space = PL.closedCube β ∧ PL.MeshLT P δ

/-- **`A2` / `G10`**: affine sub-cube maps preserve `PL.DomDim` with the same dimension. -/
def DomDimAffineForm (n : ℕ) : Prop :=
  ∀ (y₀ : PL.E n) (r : ℝ), r ≠ 0 → ∀ (A : Set (PL.E n)) (d : ℤ),
    PL.DomDim A d → PL.DomDim {z | y₀ + r • z ∈ A} d

/-- Brown's monotone-union theorem in *criterion* form: a locally compact, second countable
space in which every compact set is contained in an open `n`-cell is an open `n`-cell. -/
def BrownCriterion (n : ℕ) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X],
    (∀ K : Set X, IsCompact K → ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ PL.IsOpenCell n U) →
    Nonempty (X ≃ₜ PL.E n)

/-- `BrownCriterion` with its universe pinned by the space `M`, so that it can be applied to
`M` and to subspaces of `M` inside a proof.  Definitionally `BrownCriterion n`, and any proof
of the latter (e.g. `Work.Brown.brownCriterion n`, proved for all universes) supplies it. -/
def BrownCriterionAt (n : ℕ) (M : Type u) : Prop := BrownCriterion.{u} n

def RadialExpandForm (n : ℕ) : Prop :=
  ∀ (ε R : ℝ), 0 < ε → ε < R → ∃ g : PL.E n ≃ₜ PL.E n, g 0 = 0 ∧
    (∀ x, R + 1 ≤ ‖x‖ → g x = x) ∧ ∀ x, ε ≤ ‖x‖ → R ≤ ‖g x‖

/-- The hypotheses coming from the other areas of the blueprint, bundled.  Instantiating this
is the only work the assembly has to do in order to use `connell_step`.

The parameter `M` only serves to pin the universe at which the bundled statements are
available (so that they can be applied to `M` and to its open subspaces). -/
structure Assumptions (n : ℕ) (M : Type u) where
  /-- blueprint `E0` (area `A9`) -/
  engulf : EngulfForm.{u} n
  /-- blueprint `G7` (area `A6`) -/
  skeleton : SkeletonData n
  /-- blueprint `G8` (area `A7`) -/
  annulus : AnnulusForm n
  /-- blueprint `C1` (area `A7`) -/
  cubeMinus : CubeMinusForm.{u} n
  /-- blueprint `C0` (area `A7`) -/
  extHomeo : ExtHomeoForm.{u} n
  /-- blueprint `A7` -/
  locCubeOpen : LocCubeOpenForm.{u} n
  /-- blueprint `G7`/`A2`: cube triangulations -/
  triangulation : CubeTriangulationForm n
  /-- blueprint `G10`/`A2`: affine invariance of `PL.DomDim` -/
  domDimAffine : DomDimAffineForm n

end Work.Cells.Connell
