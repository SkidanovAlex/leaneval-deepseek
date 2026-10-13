/-
Area DZA: vocabulary module for the chart-ring/degree-zero identification.

Re-exports `Work.DSEQP.gf_bridge` (which defines the chart vocabulary `Work.DSEQP.xS`,
`Work.DSEQP.awayRes`, `Work.DSEQP.AtoAway`, the global grading instance and the `A`-algebra
structure on the chart rings) together with the `Work.DSCOH` chart-localization API used by the
proof of `Work.DSEQP.DZA.gf_degzero_away`.
-/
import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSCOH.resAt_degZero
import Submission.Work.DSCOH.resAt_divPow_toLoc
import Submission.Work.DSCOH.resAt_id
import Submission.Work.DSCOH.resAt_comp
import Submission.Work.DSCOH.degZero_exists_repr
