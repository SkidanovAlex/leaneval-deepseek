import Mathlib
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.ezaw_homotopy_of_W
import Submission.Work.Kunneth.ezaw_W_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

theorem ez_aw_homotopy (X Y : SSet) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (Work.Kunneth.ezMap X Y) (Work.Kunneth.awMap X Y))
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.tChain X Y))) := by
  obtain ⟨W, hW⟩ := ezaw_W_exists
  exact ezaw_homotopy_of_W W hW X Y

end Work.Kunneth
