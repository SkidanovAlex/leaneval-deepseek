import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.PolynomialKernel

/-!
# Re-export of the fixed interfaces for the `Oscillation` area

This module exists so that delegated lemmas inside `Submission/Work/` can import the fixed
statement files `Submission.BourgainPlan.Interfaces` and `Submission.PolynomialKernel`
(the `depends_on` mechanism of the harness resolves paths relative to `Submission/Work/`).
-/
