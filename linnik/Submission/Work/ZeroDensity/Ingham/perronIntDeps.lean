import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.Analysis.Complex.Gamma_vertical_norm_bounds
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs
import Submission.Work.ZeroDensity.Ingham.Defs

/-!
# Dependency aggregator for `Work.ZeroDensity.Ingham.perronIntIntegrableSelf`

The `depends_on` mechanism of the delegation tool resolves module paths under `Submission/Work/`,
so this module re-exports the ingredients that live outside `Submission/Work/`:

* `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth` — `zeta_strip_polyGrowth` for `-1 ≤ σ ≤ 3`;
* `Commons.Analysis.Complex.Gamma_vertical_norm_bounds` — `gamma_strip_upper`, `gamma_upper_main`,
  `norm_Gamma_le_shift_nat`, `K6`, ...;
* `Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp` —
  `integrable_one_add_abs_rpow_exp : Integrable (fun t => (1 + |t|) ^ c * exp (-(a * |t|)))`;
* `Work.ZeroDensity.Ingham.zetaPerronDefs` — `perronInt`, `perronM`, `perronH` and the
  decomposition `perronInt_eq_perronM_div`.
-/
