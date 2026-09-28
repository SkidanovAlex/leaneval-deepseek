import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Projective.GoodCp2.fork.pd_good_list_pieces
import Submission.Work.Projective.GoodCp2.fork.pd_good_open_subset_chartBall
import Submission.Work.Cohomology.pd_good_univ

/-!
# `pd_good_univ` — import shim of the ISLANDS2 subproject

This file used to declare a **duplicate copy** of the module

* `Submission.Work.Cohomology.pd_good_univ`

(the declarations were verbatim copies: same names, same statements, same proofs).  The duplicate
made the two copies mutually unimportable — Lean refuses an environment that contains two
declarations with the same name — so the copies could not meet in the final assembly
(`Submission/Work/Islands2/AllCritical.lean`).

The ISLANDS2 subproject has removed the duplicate: this module is now a thin **shim** that simply
imports the original, so every name it used to export is still available under exactly the same
name and with exactly the same statement.  Nothing else changed; no consumer needs to be updated.
See `Submission/Work/Islands2/README.md` for the full inventory of duplicates.
-/
