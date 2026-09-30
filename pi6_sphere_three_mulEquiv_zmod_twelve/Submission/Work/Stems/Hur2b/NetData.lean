import Mathlib
import Submission.Work.Stems.Hur2b.NetLayout

/-!
# The index data of the T-net, its collar, and the boundary behaviour of the readings

`NetLayout.lean` defines the six cells of the T-net (as subsets of `I²`) and the reading of each of
them onto its face of `∂I³`.  This file adds

* `netCellIdx`, the six grid cells as pairs of indices of the uniform `8 × 8` grid;
* `openCube`, the *open* grid cell, and `openNetCell`, the open cells of the T-net;
* `netRead_mem_skel`, the fact that each reading maps the *boundary* `∂I²` into the `1`-skeleton
  `Skel3` of `∂I³` (this is what makes the cell-readings based cubes).

The statements about the *collar* of the T-net (a continuous `ψ : I² → ∂I³` which is `v` on `∂I²`,
agrees with the readings on the six net cells, and maps the complement of those cells into the
`1`-skeleton) are made in the module `Submission.Work.Stems.Hur2b.net_model`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- The grid cell carrying the `k`-th piece of the T-net, as a pair of indices of the uniform
`8 × 8` grid: `(2,3), (3,3), (4,3), (5,3)` (the belt) then `(3,2)` and `(3,4)` (the two caps). -/
def netCellIdx : Fin 6 → Fin 8 × Fin 8
  | 0 => (2, 3)
  | 1 => (3, 3)
  | 2 => (4, 3)
  | 3 => (5, 3)
  | 4 => (3, 2)
  | 5 => (3, 4)

/-- The *open* grid cell `(i,j)`. -/
def openCube (i j : Fin 8) : Set (IC 2) :=
  {y | (i : ℝ) / 8 < (y 0 : ℝ) ∧ (y 0 : ℝ) < ((i : ℝ) + 1) / 8 ∧
       (j : ℝ) / 8 < (y 1 : ℝ) ∧ (y 1 : ℝ) < ((j : ℝ) + 1) / 8}

/-- The open cells of the T-net: their complement is the collar of the net. -/
def openNetCell (k : Fin 6) : Set (IC 2) :=
  openCube (netCellIdx k).1 (netCellIdx k).2

/-- **The collar of the T-net**: the set of points of `I²` lying in no open net cell. -/
def Collar : Set (IC 2) := {y | ∀ k : Fin 6, y ∉ openNetCell k}

@[simp] theorem mem_Collar {y : IC 2} :
    y ∈ Collar ↔ ∀ k : Fin 6, y ∉ openNetCell k := Iff.rfl

end

end Work.Stems.Hur2b
