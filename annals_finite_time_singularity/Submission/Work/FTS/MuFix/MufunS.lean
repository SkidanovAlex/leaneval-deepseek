/-
# `Submission/Work/FTS/MuFix/` — the μ sign fix, option (a′)

Owner's entry point for the area.  The **deliverable module of the fix itself** is
`Submission/Work/Construction/MufunS.lean` (module `Submission.Work.Construction.MufunS`,
namespace `Work.Construction`), which the ruling `Submission/Work/FTS/FTS_MUFUN_SIGN.md` §5 asks to
be created "in place" next to `Construction.Defs`.  This file is a *pointer* to it: importing
`Submission.Work.FTS.MuFix.MufunS` makes the corrected constant and its API available inside the
`MuFix` area, so that the check files in `MuFix/` do not have to reach outside.

Nothing is defined here — in particular this module must **not** be imported together with
`Submission.Work.Construction.MufunS` *as a second definition of `mufunS`*: it only re-exports.

Contents of the area (see `APPLY.md`, `NOTES.md`):

* `Work/Construction/MufunS.lean` — `mufunS`, `L12_neg`, `L12_transport_neg`,
  `mufunS_eq_mufun_neg`, `two_mul_mufunS`, `mufunS_eq_mufun_iff`, `mu_bound_mulS`, `mu_boundS`;
* `MuFix/SignCheck/*.lean` — the sign-flipped re-proofs of the six theorems the rebuild would
  otherwise have to re-prove by hand (`muDyn_smallS`, `muDyn_small_quadS`, `muDyn_small_of_H4S`,
  `muDyn_abs_sub_le_threeS`, `MuEstimateS`, `MuEstimateScaledS`, `MuEstimateQS`,
  `muDynStar_eq_mufunS`), plus `ArithProbe.lean` with the pure-arithmetic proof blocks of the
  drafts;
* `MuFix/drafts/**` — the patched copies of the 22 live files that must change, one per
  `drafts/<path relative to Submission/>.lean.txt`;
* `MuFix/APPLY.md` — the copy list, in dependency order, plus what to expect to rebuild.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
