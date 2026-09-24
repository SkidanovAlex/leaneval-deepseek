import Submission.Commons.Analysis.Oscillatory.van_der_corput_bound
import Submission.Commons.Analysis.Oscillatory.poly_first_derivative_test
import Submission.Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp

/-!
# Convenience re-exports for the `S₂` area

Importing this module brings into scope the van der Corput toolkit of `Submission.Commons`:
* `Commons.Analysis.Oscillatory.vdc_first_deriv` — the first-derivative (monotone phase) bound
  `‖∫_a^b e^{iφ}‖ ≤ 4/λ` when `|φ'| ≥ λ` (`poly_first_derivative_test`);
* `Commons.Analysis.Oscillatory.vdcBound`/`vdc_two` — the second-derivative bound
  `‖∫_a^b e^{iφ}‖ ≤ C/λ^{1/2}` when `|φ''| ≥ λ` (`van_der_corput_bound`).

Files under `Submission/Work/` cannot list `Submission/Commons/...` in `depends_on`, hence this
re-export module.
-/
