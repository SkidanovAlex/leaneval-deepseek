import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.Tools
import Submission.Work.Serre.CellStep.compressRel_cellU
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.RatHurewicz.CompressRelToRelPi

set_option synthInstance.maxHeartbeats 400000


/-!
# `serreC0KillHomology`: the vocabulary

For `n ≥ 1`, a space `Y`, an index type `ι` and attaching maps `f : ι → C(S^{n+1}, Y)`, the space
`X = attachCells n Y ι f` is `Y` with `(n+2)`-cells glued on.  The theorem
`Work.Serre.serreC0KillHomology` computes

`H_{n+1}(X;ℤ) ≅ H_{n+1}(Y;ℤ) ⧸ span{hurewiczClass (f i)}`.

The proof uses the Mayer–Vietoris sequence of the open cover of `X` by

* `KillU` — the "outer" part: the complement of the images of the closed model balls of radius
  `1/4` (this contains the old space `KillA` and is a strong deformation retract of it), and
* `KillV` — the "inner" part: the union of the images of the open model balls of radius `1/2`.

Their intersection `KillZ = KillU ∩ KillV` is the union of the images of the model shells
`{1/4 < ‖x‖ < 1/2}`, i.e. of the `KillQ i`, which are pairwise disjoint open sets, each
homeomorphic to the model shell (hence homotopy equivalent to `S^{n+1}`).

This file fixes the vocabulary only; every statement about it is proved elsewhere.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- The space obtained from `Y` by attaching the `(n+2)`-cells along `f`. -/
abbrev KillX (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) : Type :=
  Work.RatHurewicz.attachCells n Y ι f

/-- The "old part" of `KillX f`, i.e. the image of `Y`. -/
def KillA (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) : Set (KillX f) :=
  Set.range (Work.RatHurewicz.attachIncl n Y ι f)

/-- The outer member of the cover: the complement of the images of the closed model balls of
radius `1/4`.  It contains `KillA f`. -/
def KillU (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) : Set (KillX f) :=
  cellU f (1 / 4)

/-- The inner member of the cover: the union of the images of the open model balls of radius
`1/2`. -/
def KillV (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) : Set (KillX f) :=
  cellV f (1 / 2)

/-- The `i`-th shell piece: the points of the `i`-th cell of norm between `1/4` and `1/2`. -/
def KillQ (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) : Set (KillX f) :=
  cellImg f i (cellOpenBallSet n (1 / 2)) ∩ (cellBallImg f (1 / 4))ᶜ

/-- The intersection of the two members of the cover, i.e. the union of the shell pieces. -/
def KillZ (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) : Set (KillX f) :=
  KillU f ∩ KillV f

end

end Work.Serre
