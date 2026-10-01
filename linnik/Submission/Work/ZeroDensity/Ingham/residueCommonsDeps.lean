import Mathlib
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs

/-! Dependency shim: re-exports the `Commons` Gamma vertical-norm bounds (in particular the
explicit constant `Commons.Analysis.Complex.K11` and `gamma_upper_final`) together with the
Ingham zero-detector vocabulary, so that lemmas living under `Submission/Work` can depend on
them through the delegation machinery. -/
