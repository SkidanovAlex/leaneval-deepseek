import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Work.SSGRoute.placePrime_eq_of_val_lt_one
import Submission.Work.SSGRoute.dvd_discr_of_isRamifiedIn
import Submission.NK.WeakNU.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared imports for the `T⁰`-disjointness lemmas

This module is a pure-import module: it gathers, for the deferred lemmas about
`Work.SSGRoute.exists_T0_split_generating_disj`, the vocabulary they need
(`SSGRoute.IsFinPlace`, `SSGRoute.decomp`, `SSGRoute.IsRamifiedIn`,
`Work.SSGRoute.placePrime`, and Čebotarev's existence form
`NK.WeakNU.ChebotarevFrobeniusInput`).
-/
