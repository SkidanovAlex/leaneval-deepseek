/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.LocalField.globalCFT_localField_locallyCompactSpace
import Submission.NK.GlobalCFT.LocalField.globalCFT_localFieldUnits_locallyCompactSpace
import Submission.NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite
import Submission.NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_eventually
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Topology of the local fields and their unit groups

Collects the local (per-place) topological facts about `K_v` and `K_vˣ`:
`K_v` is locally compact, so is `K_vˣ`, `𝒪_qˣ` is compact at every finite place, hence at all
but finitely many places.

* `NK.GlobalCFT.LocalField.globalCFT_localField_locallyCompactSpace`
* `NK.GlobalCFT.LocalField.globalCFT_localFieldUnits_locallyCompactSpace`
* `NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_finite`
* `NK.GlobalCFT.LocalField.globalCFT_localUnits_isCompact_eventually`
-/
