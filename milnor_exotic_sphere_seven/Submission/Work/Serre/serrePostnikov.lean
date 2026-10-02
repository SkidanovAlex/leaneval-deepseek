import Submission.Work.Serre.Models
import Submission.Work.Serre.serrePostnikovTower

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Postnikov tower in a range

`Work.Serre.SerrePostnikov` is `Work.Serre.serrePostnikovTower`, the finite-range Postnikov tower
built by attaching cells (RATHUREWICZ's `AttachCells`).  Only the range `m < i ≤ N` is needed by
the consumers (every use of a `K(A,m)` in this project is in a bounded range of degrees).
-/

namespace Work.Serre

theorem serrePostnikov : SerrePostnikov := serrePostnikovTower

end Work.Serre
