import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re

/-!
# Prelude for the "three characters" repulsion input

Import surface for `Work.LinnikAreas.OtherCharRepel.threeCharLogDeriv` and its
helper lemmas.  It bundles, from `Submission.Commons`,

* `LFunction_logDeriv_eq_neg_LSeries_vonMangoldt` — `L′/L(s,χ)` is minus the twisted
  von Mangoldt L-series on `Re s > 1`;
* `norm_char_nat_le_one` — `‖χ n‖ ≤ 1`;
* `summable_vonMangoldt_div_rpow` — summability of `Λ(n)/n^σ` for `σ > 1`;

together with `Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re`, the same
identity for `ζ`.
-/
