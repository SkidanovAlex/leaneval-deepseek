import Submission.Work.Serre.Models
import Submission.Work.Serre.serrePostnikovTower

/-!
# The Postnikov tower in a range

`Work.Serre.SerrePostnikov` is `Work.Serre.serrePostnikovTower`, the finite-range Postnikov tower
built by attaching cells (RATHUREWICZ's `AttachCells`).  Only the range `m < i ≤ N` is needed by
the consumers (every use of a `K(A,m)` in this project is in a bounded range of degrees).
-/

namespace Work.Serre

theorem serrePostnikov : SerrePostnikov := serrePostnikovTower

end Work.Serre
