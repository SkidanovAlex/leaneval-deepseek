/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B)

# Area BNChart — everything

Import this module to get the whole chapter of area `BNChart`: the Riemann–Roch data of a
concrete curve in successor shape, the Brill–Noether chart over the base field, the RESID data
and COV′.  See `Submission/Work/BNChart/NOTES.md`.
-/
import Submission.Work.BNChart.Basic
import Submission.Work.BNChart.Chart
import Submission.Work.BNChart.ChartData
import Submission.Work.BNChart.BNData
import Submission.Work.BNChart.Resid
import Submission.Work.BNChart.reduced_nonspecial_support
import Submission.Work.BNChart.evalSection_eq_evalAt
import Submission.Work.BNChart.iOf_eq_zero_of_det_ne_zero_point
import Submission.Work.BNChart.det_ne_zero_of_iOf_eq_zero
import Submission.Work.BNChart.exists_reduced_nonspecial_chart
import Submission.Work.BNChart.sum_smul_fieldMap_canonBasis_mem_L
import Submission.Work.BNChart.sum_smul_fieldMap_canonBasis_ne_zero
import Submission.Work.BNChart.exists_coeff_mem_L_pullK_rochW
import Submission.Work.BNChart.ordAt_pos_of_evalSection_sum_eq_zero
import Submission.Work.BNChart.Criterion
import Submission.Work.BNChart.Main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

