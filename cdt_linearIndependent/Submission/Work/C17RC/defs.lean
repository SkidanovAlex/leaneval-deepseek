import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.Work.C17.roots_sum_div_derivative

/-!
# Shared imports for the `Work.C17RC` Riccati lemmas

This tiny module exists so that lemmas delegated in the `Work.C17RC` directory can refer to
`Submission.CDT.dRat` (the derivative of a rational function) and to
`Work.C17.roots_sum_div_derivative` (the Lagrange/residue identity
`sum over the roots beta of B of A(beta)/B'(beta) = A.coeff (deg B - 1)`) while keeping
their `depends_on` lists inside `Submission/Work`.

Nothing is proved here; the file only re-exports those imports.
-/
