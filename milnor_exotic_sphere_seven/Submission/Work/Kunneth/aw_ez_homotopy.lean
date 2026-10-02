import Mathlib
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.EZHom2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Kunneth

theorem aw_ez_homotopy (X Y : SSet) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (Work.Kunneth.awMap X Y) (Work.Kunneth.ezMap X Y))
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.sChain (Work.Kunneth.sProd X Y)))) :=
  EZHom.aw_ez_homotopy_aux X Y

end Work.Kunneth
