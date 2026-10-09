import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_vocab
import Submission.Work.SSGRoute.step4_y_escape_v2.ChebotarevSplit
import Submission.Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split
import Submission.Work.SSGRoute.step4_y_escape_v2.ReadOff
import Submission.Work.SSGRoute.EscapeCoreLib.classField_stable_open_finiteIndex
import Submission.Work.SSGRoute.EscapeCoreLib.algEquiv_extend_compositum
import Submission.Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.NK.Chebotarev.FrobRestriction
import Submission.Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Import cone of the Grünwald-with-escape lane

This module collects, in one place, the modules the escape lane
(`Work.SSGRoute.GrunwaldEscapeCore`) consumes: the vocabulary (`gesU`, `gesKConj`), the
class-field-theoretic tools of `EscapeCoreLib`, Čebotarev over an arbitrary number-field base
(`ssg8Chebotarev`, `ZDataTwo.chebotarev_frobenius_split`), the ray-class Čebotarev
(`step4_y_escape_v2.ChebotarevSplit`, `RayClass`), the reading-off of the subgroup `U`
(`step4_y_escape_v2.ReadOff`), the local Kummer dictionary and the inertia criterion for the
Kummer character (`ZConstruction.localKummerDictionary`,
`kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd`), and the level-`K` Kummer cochain
(`ZSplit.SWFourOddKummer`).

It exists so that statements of the lane can be delegated with a single `depends_on` entry.

It must NOT import `grunwald_escape_support_E`: that module is a *consumer* of the hub's users
(`gesCorrectionL1K`), and importing it here closes the cycle

  `support_E -> gesCorrectionL1K -> grunwald_escape_relative_L1K -> ... -> EscapeImports`

(see `Submission/Work/GrunwaldEscapeCore/PING_import_cycle_L1K.md`).  Nothing in this hub uses a
declaration of `grunwald_escape_support_E`, and every module that uses the `ges_*` transport lemmas
imports `grunwald_escape_support_E` directly, so the edge is redundant. -/
