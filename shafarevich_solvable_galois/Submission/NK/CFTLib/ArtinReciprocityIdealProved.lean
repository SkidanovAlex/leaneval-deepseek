import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.NUV2.chebotarev_all0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! The ideal-theoretic Artin reciprocity law, closed (orchestrator glue): Lang's cyclic case from the proved
Artin lemma `NK.CFTLib.ARL.auxField_exists_B` and the proved transfer `NK.NUV2.ChebAux.kernelLe_of_auxField`. -/

namespace NK.CFTLib

theorem artinReciprocityIdeal_proved : NK.CFTLib.ArtinReciprocityIdeal :=
  NK.NUV2.artinReciprocityIdeal_of_auxField
    (fun K L _ _ _ _ _ _ _ _ _ m hm => NK.NUV2.ChebAux.kernelLe_of_auxField K L m hm)
    (fun K L _ _ _ _ _ _ _ _ m hm => NK.CFTLib.ARL.auxField_exists_B K L m hm)

end NK.CFTLib
