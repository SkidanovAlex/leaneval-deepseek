import Mathlib
import Submission.Work.Kunneth.AW
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.EZHom2

namespace Work.Kunneth

theorem aw_ez_homotopy (X Y : SSet) :
    Nonempty (Homotopy
      (CategoryTheory.CategoryStruct.comp (Work.Kunneth.awMap X Y) (Work.Kunneth.ezMap X Y))
      (CategoryTheory.CategoryStruct.id (Work.Kunneth.sChain (Work.Kunneth.sProd X Y)))) :=
  EZHom.aw_ez_homotopy_aux X Y

end Work.Kunneth
