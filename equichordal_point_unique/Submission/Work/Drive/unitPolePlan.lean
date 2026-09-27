/-
# Plan for `Work.Drive.exists_member_sweepFamily_unitPole` (and its sibling
# `Work.Drive.extremal_zero_factorization`)

This module carries no declarations; it is the *construction plan* that the requested lemma
`Work.Drive.exists_member_sweepFamily_unitPole` is meant to be proved by.  Read it before starting.

## Setting

`c := chartAt ℂ y`, `a := c y`.  The hypotheses give a holomorphic `h : X → ℂ` with `‖h‖ ≤ 1`,
`h y = 0`, and local data `ρ ≤ r`, `k ≥ 1`, `ψ`, `0 < m`, `1 ≤ M`, `m ≤ M` with

* `closedBall a r ⊆ c.target`,
* `M * ρ ^ k ≤ 1`,
* `(h ∘ c.symm) w = (w - a)^k * ψ w` and `m ≤ ‖ψ w‖ ≤ M` for `dist w a < r`.

In particular, on the chart ball `D := chartBall c a r` (= `c.source ∩ c ⁻¹' ball a r`), `h` has
`y` as its only zero, the zero has order exactly `k`, and `‖h z‖ = ‖c z - a‖^k · ‖ψ (c z)‖`
with `‖ψ (c z)‖` between `m` and `M`.

Choose the clamp constant

  `K := max 0 (-(Real.log ((r / 2) ^ k * m)))`

(any `K ≥ 0` with `K ≥ -log ((r/2)^k * m)` works), and put

  `v z := (if z ∈ D then (1 / k) * (-Real.log ‖h z‖) else (1 / k) * clampedLogNorm h K z)`

with `clampedLogNorm` from `Submission.Work.SimplyConnected.ABS.sweep_domination_aux`
(`clampedLogNorm g K z = -log (max ‖g z‖ (exp (-K)))`, so it is `K` at the zeros of `g` and
`-log ‖g z‖` where `-log ‖g z‖ ≤ K`; it is superharmonic on `X`, and
`clampedLogNorm_of_le`, `clampedLogNorm_eq_min`, `clampedLogNorm_of_zero`,
`clampedLogNorm_le_neg_log`, `clampedLogNorm_nonneg` and `superharmonicOnX_clampedLogNorm` are
the lemmas to use).

## Membership in the sweep family (`Submission.sweepFamily (greenBarrier y ρ) (univ \ {y})`)

A member is a pair `<SuperharmonicOnX v (univ \ {y}), ∀ x ∈ univ \ {y}, greenBarrier y ρ x ≤ v x>`.

### Superharmonicity

`Submission.SuperharmonicOnX := ContinuousOn v U ∧ ∀ x ∈ U, SuperharmonicOnXAt v x`
(`Submission.SuperharmonicOnXAt.congr` is the localisation lemma, `Submission.SuperharmonicOnXAt.min`,
`.const_mul`, `Submission.harmonicOnXAt_neg_log_norm`, `Submission.harmonicOnXAt_const`,
`Submission.continuous_clampedLogNorm` are the basic inputs).  Prove `SuperharmonicOnXAt v p` for
`p ∈ U = univ \ {y}` by *supplying a local model*, in three cases:

1. `p ∈ D`: `v =ᶠ (1/k) * (-log ‖h ·‖)` near `p` (because `D` is open) and that function is
   *harmonic* at `p`: `h p ≠ 0` because `p ∈ D`, `p ≠ y` and `p ∈ D ⟹ c p ≠ a` while
   `h p = (c p - a)^k ψ (c p)`; use `harmonicOnXAt_neg_log_norm` then `.const_smul (1/k)` and
   `SuperharmonicOnXAt.congr`.
2. `p ∉ closure D`: `v =ᶠ (1/k) * clampedLogNorm h K` near `p` (the complement of `D` is a
   neighbourhood of `p`), and that function is superharmonic
   (`superharmonicOnX_clampedLogNorm` then `SuperharmonicOnX.const_mul`).
3. `p ∈ ∂D` (`dist (c p) a = r`): the two models agree on the annulus
   `N := {z | r/2 < dist (c z) a} ∩  c.source` (a neighbourhood of `p`): for `z ∈ N ∩ D` one has
   `r/2 ≤ ‖c z - a‖ < r`, so `‖h z‖ ≥ (r/2)^k * m`, i.e. `-log ‖h z‖ ≤ K`; hence
   `(1/k) * (-log ‖h z‖) = (1/k) * clampedLogNorm h K z`.  For `z ∈ N \ D` the two sides agree by
   definition of `v`.  So `v =ᶠ (1/k) * clampedLogNorm h K` near `p` and case 2 applies.

Then `ContinuousOn v U` follows by `continuousOn_of_forall_continuousAt` with the same three local
models (in case 1 use continuity of `x ↦ -log ‖h x‖` at `p`, where `h p ≠ 0`; in cases 2/3 the
continuity of `clampedLogNorm`).

### Domination of the barrier

For `x ≠ y` (`from now on z := c x`, and recall `c x ≠ a`):

* if `x ∈ chartBall c a ρ` (so `x ∈ D` because `ρ ≤ r`): `greenBarrier y ρ x = log (ρ / ‖c x - a‖)`
  (`chartLogClamp_of_mem`), and `v x = (1/k) * (-log ‖h x‖)` with
  `‖h x‖ = ‖c x - a‖^k * ‖ψ (c x)‖ ≤ ‖c x - a‖^k * M ≤ (‖c x - a‖ / ρ)^k` (this is where
  `M * ρ^k ≤ 1` enters, i.e. `log ρ ≤ -(1/k) log M`); taking `-(1/k) log` gives
  `v x ≥ -log (‖c x - a‖ / ρ) = log (ρ / ‖c x - a‖)`;
* if `x ∉ chartBall c a ρ`: `greenBarrier y ρ x = 0` (`chartLogClamp_of_not_mem`) and `v x ≥ 0`:
  inside `D` this is `‖h x‖ ≤ 1`, outside `D` it is `clampedLogNorm_nonneg` with `0 ≤ K` and
  `‖h‖ ≤ 1`.

## The unit pole

For `x ∈ chartBall c a ρ`, `x ≠ y`, with `w := c x` (`‖w - a‖ < ρ ≤ r`):

  `v x + log ‖w - a‖ = (1/k) * (-log (‖w - a‖^k * ‖ψ w‖)) + log ‖w - a‖
                     = -(1/k) * log ‖ψ w‖ ≤ -(1/k) * log m`,

because `m ≤ ‖ψ w‖`, `0 < m`, `0 < ‖w - a‖`.  So `C := -(1/k) * Real.log m` works
(`Real.log_le_log`, `Real.log_mul`, `Real.log_pow`; note `-log` of a positive quantity).
-/
import Submission.Work.Drive.weakcase_deps
