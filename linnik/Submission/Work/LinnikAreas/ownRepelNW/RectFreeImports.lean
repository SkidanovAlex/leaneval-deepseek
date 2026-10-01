/-
# `RectFreeImports`: the `pfP`-clash-free import bridge for zero-sum/zero-count work

`Submission/Commons/NumberTheory/Linnik/completedL_pf_identity_rect.lean` and
`Submission/Commons/NumberTheory/Linnik/logDeriv_pf_identity.lean` both declare
`Commons.NumberTheory.Linnik.pfP`, so no single Lean environment can contain both (see
`NOTE_pfP_import_clash.md` in this directory).  Modules mentioning `Work.LinnikAreas.DhK.kMult`
or `Work.LinnikAreas.DhK.Xi` must import `Submission.Work.LinnikAreas.DhK.Defs`, whose closure
contains `logDeriv_pf_identity`; for them the whole `..._pf_identity_rect` family (and in
particular `Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform`, whose
closure reaches `BombieriVinogradov.siegel_walfisz_chi -> completedL_pf_diff_norm_le`) is
unusable.

This module re-exports, under a single `Work`-rooted path, the *rect-free* half of the
inverse-square / divisor toolkit, so that a delegated lemma (or a `DhK`-side consumer) can depend
on it via the delegation tool's `Submission/Work/`-relative path convention:

* `Commons.Analysis.Asymptotics.invSq_zeroSum_of_count_uniform` — the dyadic inverse-square
  estimate with the constant uniform in the count parameter `q`, plus its elementary layer lemmas
  `log_add_two_pow_le`, `four_div_pow_mul_le`, `geom_layer_sum_bound`, `indicator_closedBall_eq`
  and the per-point layer bound `Commons.Analysis.Dyadic.invSq_le_dyadic_layer`;
* `Commons.Analysis.Complex.finsetDivisor_tools` — `finset_sum_le_finsum_of_nonneg`,
  `indicator_divisor_le_divisorBall`, `indicator_divisorBall_le_divisorBallFinsum`,
  `finset_orderSum_le_divisorFinsum` (the "shrink a finite set into a ball" step, and the
  indicator transfer used to feed a ball-count hypothesis to the dyadic estimate);
* `Commons.NumberTheory.Linnik.completedL_ballZeroCount` and
  `Commons.NumberTheory.Linnik.zerosInStrip`-style inputs are available separately; the *uniform*
  zero count that is compatible with this bridge is
  `Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5`.
-/
import Mathlib
import Submission.Commons.Analysis.Asymptotics.invSq_zeroSum_of_count_uniform
import Submission.Commons.Analysis.Complex.finsetDivisor_tools

open scoped BigOperators
