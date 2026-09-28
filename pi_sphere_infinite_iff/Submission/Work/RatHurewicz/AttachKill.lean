import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Stems.Hurewicz

/-!
# Killing a homotopy group by attaching cells

Area **RATHUREWICZ**, C0/K1 of the Serre blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md`).
`Work.RatHurewicz.attachCells n Y ι f` attaches `(n+2)`-cells to `Y` along the attaching maps
`f i : S^{n+1} → Y`.  To *kill* `π_{n+1}(Y,y₀)` one attaches one cell per element of that group,
along a map out of the sphere representing it; this module fixes that family.

A class `α : π_{n+1}(Y,y₀)` is represented by a based cube `I^{n+1} → Y`, which descends to a map
`S^{n+1} → Y` along the collapse `Work.Stems.collapseMap`; that descent is
`Work.Stems.cubeLift`, and `Work.Stems.cubeLift_comp` records that it restricts to the cube on the
cube. -/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **The family of attaching maps that kills `π_{n+1}`**: one `(n+2)`-cell per element of
`π_{n+1}(Y,y₀)`, attached along the sphere map represented by that element. -/
def killFamily (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y) :
    HomotopyGroup (Fin (n + 1)) Y y₀ → C(cellSphere n, Y) :=
  fun α => Work.Stems.cubeLift (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Quotient.out α)

/-- The attaching map of the cell of a class is the collapse of a representative cube of that
class. -/
theorem killFamily_apply (n : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (α : HomotopyGroup (Fin (n + 1)) Y y₀) :
    killFamily n Y y₀ α =
      Work.Stems.cubeLift (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Quotient.out α) := rfl

end

end Work.RatHurewicz
