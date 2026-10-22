/-
The `CWTOP` structure files (`Submission.Work.CWTOP.Basic` and the re-export module
`Submission.Work.CWTOP.Closed`) are under active construction by other members of the team, so this
file depends only on the fixed interface module, where `CWClosed` is defined.
-/
import Mathlib
import Submission.Blueprint.Interfaces

namespace Work.CWTOP

/-- A contractible Hausdorff space is homotopy equivalent to a point, hence lies in any
`CWClosed` class. -/
theorem g_of_contractible (G : TopCat.{0} → Prop) (hG : Submission.Blueprint.CWClosed G)
    (Y : TopCat.{0}) [T2Space Y] [ContractibleSpace Y] : G Y := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv Y PUnit
  exact hG.of_homotopyEquiv Y (TopCat.of PUnit) e hG.point

end Work.CWTOP
