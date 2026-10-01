/-
Import shim: re-exports the `Commons` analytic inputs (the vertical-strip `Γ` bound of
`Gamma_vertical_norm_bounds` and `zeta_strip_polyGrowth`) so that lemmas in
`Submission/Work/ZeroDensity/Ingham/` can depend on them through the `Work` import path.
-/
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth

open scoped Classical BigOperators
