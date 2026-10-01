/-
# `szPrelude` — shared import surface for the `siegelZeroSimple` sub-lemmas

Bundles the analytic-number-theory inputs used by the pieces of
`Work.LinnikAreas.siegelZeroSimple`:

* `Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound` — `Re(−ζ′/ζ)(σ) ≤ 1/(σ−1) + C`;
* `Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le` —
  `logDeriv_completedLFunction_eq_add` (`Λ′/Λ = L′/L + (gammaFactor)′/(gammaFactor)`),
  `norm_logDeriv_Gammaℝ_le`, and `gammaFactor_ne_zero_of_re_pos`;
* `Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt` —
  `L′/L(s,χ) = −LSeries ((vonMangoldt ·) * χ)` for `re s > 1`;
* `Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le` — the
  divisor-weighted (multiplicity-aware) bound for the rebased Hadamard partial fraction;
* `Commons.NumberTheory.Linnik.completedL_zero_strip` — zeros lie in the open strip;
* `Commons.NumberTheory.DirichletCharacter.zerosInStrip` — every zero of `Λ` has `0 < re < 1`.

## Hints for the three sub-lemmas

* `siegelZeroSimple_ldUpper` (upper bound for `Re (Λ′/Λ)(σ)`, `1 < σ ≤ 5/4`): combine
  `logDeriv_completedLFunction_eq_add` (needs `LFunction χ (σ:ℂ) ≠ 0`, available for `σ > 1`
  from `DirichletCharacter.LFunction_ne_zero_of_one_le_re`) with the *termwise* comparison
  `Re (L′/L)(σ,χ) ≤ Re(−ζ′/ζ)(σ)`.  The latter follows from
  `LFunction_logDeriv_eq_neg_LSeries_vonMangoldt` for the left side and (Mathlib)
  `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` for the right side,
  together with `vonMangoldt n * χ n ≥ − vonMangoldt n` pointwise (both series are
  absolutely convergent for `σ > 1`).  Then `zeta_logDeriv_re_axis_bound` gives the
  `1/(σ−1) + C` shape; the archimedean part `logDeriv (gammaFactor χ)` is bounded by
  `norm_logDeriv_Gammaℝ_le` (apply it at `σ` or at `σ+1` after
  `χ.even_or_odd`, cf. the private proof of `logDeriv_gammaFactor_re_le` in
  `Commons/…/LFunction_zeroFree_uniform_realAxis.lean`).

* `siegelZeroSimple_zeroSum` (multiplicity lower bound `m/(σ−β) ≤ (Λ′/Λ)(σ) + log N + …`):
  specialize `finsum_divisor_re_inv_sub_le` with `T = 0`, `σ₁ = σ`, `B₁ = B` and `R = 2`
  (the statement holds for *every* `R`; the divisor sums are monotone in `R`).  Extract the
  single term `u = β`: its divisor weight is `analyticOrderNatAt Λ β`, as it is
  `MeromorphicOn.divisor`, via `Work.LinnikAreas.divisor_eq_analyticOrderNatAt`
  (`Submission/Work/LinnikAreas/FamilyZeroCountNonPrincipal.lean`) applied to
  `AnalyticOnNhd ℂ Λ (closedBall 0 R)` (use `differentiable_completedLFunction`), and its
  kernel value `(σ−β)/((σ−β)²) + (1+β)/((1+β)²)` is `≥ 1/(σ−β)`; all other terms are
  nonnegative by `zerosInStrip` (zeros satisfy `0 < re < 1`) and
  `MeromorphicOn.AnalyticOnNhd.divisor_nonneg`.
  Use `finsum_eq_sum_of_support_subset` (or `Finset.single_le_sum`) to isolate the term.

* `siegelZeroSimple_arith` (pure real arithmetic): letting `L = log q`, `t = √lam`,
  the product equals `1 + t + (C + log N + log 2/2 + 3/2)·(t+lam)/L`; use `lam ≤ 1/100`
  (`t ≤ 1/10`), `log N ≤ L` (from `N ≤ q`, `Real.log_le_log`) and pick `q₀` with
  `Real.log q₀ ≥ max 1 ((C + log 2/2 + 3/2 + 1) * 0.11 / 0.7)` — e.g. take
  `q₀ = ⌈Real.exp X⌉₊ + 2` for `X` that bound (`Real.log_exp`, `Nat.le_ceil`), or use
  `exists_nat_gt`.
-/
import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_inv_sub_le
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
