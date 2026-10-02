import Mathlib
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.RatHurewicz.AttachPush.PushOff
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.Pullback
import Submission.Work.Stems.HurewiczSphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Moore space construction: point-set definitions

Area **SERRE**, lemma `Work.Serre.serreC0Range` (C0 in range form).

For a space `Y`, an index type `ι` and attaching maps `f : ι → C(S^{n+1}, Y)`, the space
`X = Work.RatHurewicz.attachCells n Y ι f` is `Y` with `(n+2)`-cells glued on (cells of dimension
`n+2`).  This module sets up the *open cover* of `X` by

* `coverOuter f` — the complement of the set of cell centres, i.e. the "outer" part (`≃ Y`), and
* `coverInner f` — the union of the open cells, the "inner" part (each cell-contribution
  contractible),

together with their point-set properties, and the *radial push* `pushMap` of the outer part onto
`Y` (the deformation retraction given by `Work.RatHurewicz.pushGarbage` at time `1`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere n, Y)}

/-- The "outer" member of the cover of `X = attachCells n Y ι f`: the complement of the set of the
centres of the attached cells.  It contains `Y` (the range of `attachIncl`) and the punctured
cells, and it deformation retracts onto `Y` along the radial push. -/
def coverOuter (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  (Work.RatHurewicz.cellCentres n Y ι f)ᶜ

/-- The "inner" member of the cover: the union of the open cells. -/
def coverInner (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  ⋃ i, Work.RatHurewicz.cellInterior n Y ι f i

/-- The punctured open model cell: the points of norm `< 1` and `≠ 0`. -/
def punctInner (n : ℕ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | 0 < ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ ∧
    ‖((x : Work.RatHurewicz.cellDisk n) : Work.RatHurewicz.CellVec n)‖ < 1}

/-- The wedge `⋁_I S^{k+1}`, realized as a cell attachment: the cells have dimension
`(k-1) + 2 = k + 1` (meaningful for `k ≥ 1`). -/
abbrev wedgeSpace (k : ℕ) (J : Type) : Type :=
  Work.RatHurewicz.attachCells (k - 1) PUnit J
    (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere (k - 1)) PUnit.unit)

/-- The base point of the wedge `⋁_I S^{k+1}` (the common point of all the spheres). -/
abbrev wedgeBase (k : ℕ) (J : Type) : wedgeSpace k J :=
  Work.RatHurewicz.attachIncl (k - 1) PUnit J
    (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere (k - 1)) PUnit.unit) PUnit.unit

/-- The attaching maps of the wedge `⋁_I S^{k+1}` (all constant). -/
abbrev wedgeAttach (k : ℕ) (J : Type) :
    J → C(Work.RatHurewicz.cellSphere (k - 1), PUnit) :=
  fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere (k - 1)) PUnit.unit

/-- The image in `X` of the `i`-th punctured open model cell. -/
def cellPunct (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Set (Work.RatHurewicz.attachCells n Y ι f) :=
  Work.RatHurewicz.cellMap n Y ι f i '' punctInner n

end

end Work.Serre
