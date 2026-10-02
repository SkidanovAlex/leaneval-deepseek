import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `1`-cell step: vocabulary

`Z = Work.Serre.attachOneCells Y ι f` is `Y` with the intervals `D¹ = [-1,1]` attached along the
maps `f : ι → C(S⁰, Y)`.  This file fixes the vocabulary of the neighbourhood argument:

* `cellInnerOne` — the open model interval `(-1,1) ⊆ D¹`;
* `cellInteriorOne i` — the open `i`-th cell `χᵢ '' (-1,1)` in `Z`;
* `cellUnionOne U` — the union `⋃ᵢ χᵢ '' U` of the images of a subset `U` of the model interval;
* `oneCellCentreOne i` — the centre `χᵢ 0` of the `i`-th cell;
* `oneCellCentresOne` — the set of all cell centres;
* `oneCellOldPart` — the image of `Y` in `Z`.

`Z` is the disjoint union of `oneCellOldPart` and the `cellInteriorOne i` (`oneCellPartition`), each
`cellInteriorOne i` is an open copy of `(-1,1)` (`oneCellChart`), and the centres form a closed
discrete subset (`oneCellCentresOne_closed`).  These are proved in
`Submission/Work/Serre/OneCell/Geom.lean`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-- The **open model interval** `(-1,1) = D¹ ∖ S⁰`, the "inner" part of the `1`-cell. -/
def cellInnerOne : Set cellDiskOne := {x | ‖(x : ℝ)‖ < 1}

@[simp] theorem mem_cellInnerOne {x : cellDiskOne} : x ∈ cellInnerOne ↔ ‖(x : ℝ)‖ < 1 := Iff.rfl

/-- The centre `0` of the model interval, as a point of `D¹`. -/
def cellDiskOneCentreOne : cellDiskOne := ⟨0, by simp [Metric.mem_closedBall]⟩

/-- The boundary points of the model interval have norm one. -/
theorem norm_cellSphereZeroToDiskOne (z : cellSphereZero) :
    ‖((cellSphereZeroToDiskOne z : cellDiskOne) : ℝ)‖ = 1 := by
  have h : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
  have h' : ‖(z : ℝ)‖ = 1 := by simpa [dist_eq_norm] using h
  simpa [cellSphereZeroToDiskOne] using h'

theorem cellSphereZeroToDiskOne_injective : Function.Injective cellSphereZeroToDiskOne := by
  intro z z' h
  exact Subtype.ext (congrArg (fun p : cellDiskOne => (p : ℝ)) h)

/-- The **interior of the `i`-th `1`-cell**: the image of the open model interval. -/
def cellInteriorOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) : Set (attachOneCells Y ι f) :=
  oneCellMap Y ι f i '' cellInnerOne

/-- The **union of the images of a subset `U` of the model interval** under the characteristic
maps of all the cells. -/
def cellUnionOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (U : Set cellDiskOne) : Set (attachOneCells Y ι f) :=
  ⋃ i, oneCellMap Y ι f i '' U

/-- The union of the open cell interiors. -/
abbrev cellInnerUnionOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) : Set (attachOneCells Y ι f) := cellUnionOne Y ι f cellInnerOne

/-- The **centre of the `i`-th `1`-cell**, `χᵢ 0`. -/
def oneCellCentreOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) (i : ι) : attachOneCells Y ι f :=
  oneCellMap Y ι f i cellDiskOneCentreOne

/-- The set of all the centres of the attached cells. -/
def oneCellCentresOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) : Set (attachOneCells Y ι f) :=
  Set.range (oneCellCentreOne Y ι f)

/-- The **old part** of `Z`: the image of `Y`. -/
def oneCellOldPart (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) : Set (attachOneCells Y ι f) :=
  Set.range (oneIncl Y ι f)

@[simp] theorem mem_cellInteriorOne {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellSphereZero, Y)} {i : ι} {z : attachOneCells Y ι f} :
    z ∈ cellInteriorOne Y ι f i ↔ ∃ x ∈ cellInnerOne, oneCellMap Y ι f i x = z := Iff.rfl

@[simp] theorem mem_cellUnionOne {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellSphereZero, Y)} {U : Set cellDiskOne} {z : attachOneCells Y ι f} :
    z ∈ cellUnionOne Y ι f U ↔ ∃ (i : ι) (x : cellDiskOne), x ∈ U ∧ oneCellMap Y ι f i x = z := by
  simp only [cellUnionOne, Set.mem_iUnion, mem_cellInteriorOne]
  rfl

@[simp] theorem mem_oneCellOldPart {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellSphereZero, Y)} {z : attachOneCells Y ι f} :
    z ∈ oneCellOldPart Y ι f ↔ ∃ y : Y, oneIncl Y ι f y = z := Iff.rfl

@[simp] theorem mem_oneCellCentresOne {Y : Type} [TopologicalSpace Y] {ι : Type}
    {f : ι → C(cellSphereZero, Y)} {z : attachOneCells Y ι f} :
    z ∈ oneCellCentresOne Y ι f ↔ ∃ i : ι, oneCellCentreOne Y ι f i = z := Iff.rfl

end

end Work.Serre.OneCell
