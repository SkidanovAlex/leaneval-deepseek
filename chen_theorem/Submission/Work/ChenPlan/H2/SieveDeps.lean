import Mathlib
import Submission.Work.ChenPlan.H2.Sieve
import Submission.Commons.NumberTheory.Chen.vsieve_log_lower_sharp
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Vsieve_log_ratio_sharp

/-!
# Dependency bundle for the delegated `h2` lemmas

Re-exports the Mertens/Vsieve material and the per-`q` sieve setup, so that lemmas delegated
under `Submission/Work/ChenPlan/H2/` can state their results in terms of `Vsieve`,
`oddPrimLt` and `invTotient` with a single `depends_on` entry.
-/
