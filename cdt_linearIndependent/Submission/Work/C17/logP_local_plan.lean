import Mathlib

/-!
# Area C17 — the local structure of the unlikely series `Pfun` at the cusp `x_s`: plan

This file contains no mathematics; it records the decomposition of the target

```
Work.C17.logP_local_structure
```

(module `Submission.Work.C17.logP_local_structure`) as it is being proved, so that the
colleagues who prove the three supporting lemmas below can see where their piece fits.

## The target

`Pfun a b ra rb rab r0 z = Σₙ cₙ zⁿ` is the unlikely `G`-function of Theorem C.  Its Taylor
radius is `x_s = (a+√(a²−1))·(b−√(b²−1))` and it satisfies the second order Fuchsian equation

```
M(y) := P2x·y'' + P1x·y' + P0x·y = G,      G := rhoMx a b ra rb rab  (a polynomial, degree ≤ 4)
```

on the disc `‖z‖ < x_s` (this is `Submission.CDT.logP_ode`, transfered to functions).  The
leading coefficient is `P2x = (X−1)X(X+1)·Q4x`, whose zeros are the singularities of the
operator; `x_s` is one of them, and it is a *regular singular point with exponents `(0,0)`*:

```
P1x(x_s) = P2x'(x_s) ≠ 0       (this is `Work.C17.local_exp_data`).
```

Consequently every solution of `M(y) = G` near `x_s` is of the form

```
φ = κ·y₁·log(x_s − ·) + hh
```

with `y₁` a solution of the *homogeneous* equation, `y₁(x_s) ≠ 0` and `hh` holomorphic on a
ball around `x_s`; this is `Work.C17.logP_local_structure`, whose hypothesis `hnot` says that
`Pfun` has no holomorphic extension to a ball around `x_s` (that is Vivanti–Pringsheim,
`Work.C17.logP_not_holomorphic_at_xs`) — it is exactly what makes the log coefficient `κ`
nonzero.  Downstream, `Work.C17.acl_log_compare` turns the local structure into the vanishing
of `α·y₁ + β·y₁'` for the coefficients of the relation among the seventeen functions.

## The three supporting lemmas

### 1. `Work.C17f.frobenius_double_exponent_zero` (the analytic core)

The classical Fuchs/Frobenius existence theorem at a regular singular point of exponent `0`:
if `P2 = (z−s)·q` with `q` analytic at `s`, `q s ≠ 0`, `P1`, `P0` analytic at `s` and
`P1 s = q s` (the two indicial exponents are `0, 0`), then for every `a₀` the homogeneous
equation has a solution holomorphic on a ball around `s` with `y s = a₀`.

*Route.* Write `t = z − s`, `q̃(t) = q(s+t)`, `Q = q s ≠ 0`, and let `r̃(t) = (P1(s+t) − Q)/t`
(analytic at `0` because `P1 s = Q`; in Lean `dslope P1 s` — see
`Mathlib.Analysis.Calculus.DSlope`, `differentiableOn_dslope`).  With `θy = t·y'` the equation
`P2 y'' + P1 y' + P0 y = 0` is *equivalent* to

```
θ²y = b(t)·θy + c(t)·y,   b := (q̃ − Q − t·r̃)/q̃,  c := −t·P0(s+t)/q̃,
```

with `b(0) = c(0) = 0` (multiply by `t/q̃`).  So it suffices to prove the following abstract
statement, which is the cleanest form of the lemma:

```
if b, c are analytic at 0 with b 0 = c 0 = 0, then for every a₀ ∈ ℂ there are δ > 0 and
y : ℂ → ℂ with y differentiable on `ball 0 δ`, y 0 = a₀ and
z * deriv (fun w => w * deriv y w) z = b z * (z * deriv y z) + c z * y z   on `ball 0 δ`.
```

Indeed then `M(y) = (q̃(t)/t)·(θ²y − b θy − c y) = 0` on the punctured ball, hence on the whole
ball by continuity of `M(y)` at `s`.

*Proof of the abstract statement, by the Frobenius recurrence plus a majorant.*  Write
`b = Σ bᵢ tⁱ`, `c = Σ cᵢ tⁱ` (Taylor coefficients at `0`; obtain them from
`AnalyticAt.hasFPowerSeriesAt` + `FormalMultilinearSeries.ofScalars_apply_eq`, or as
`iteratedDeriv i b 0 / i!`).  Analyticity gives geometric bounds `|bᵢ| ≤ B·Tⁱ`,
`|cᵢ| ≤ C·Tⁱ` for some `B, C, T ≥ 0` (use `FormalMultilinearSeries.le_mul_pow_of_radius_pos`,
or `Commons.Analysis.Complex.cauchy_coeff_bound`, or
`Commons.Analysis.Analytic.coeff_growth_of_analyticAt`).  Define the sequence `(aₖ)` by
`a₀` and the recurrence obtained from the coefficient of `tᵏ`:

```
k² aₖ = Σ_{i=1}^{k} (bᵢ (k − i) + cᵢ) a_{k−i}          (k ≥ 1)
```

(the factor `k²` is the indicial value; it is nonzero for `k ≥ 1`).  If `|bᵢ| ≤ B Tⁱ`,
`|cᵢ| ≤ C Tⁱ` and `S > T`, then strong induction gives `|aₖ| ≤ A·Sᵏ` for suitable `A`
(uniform in `k`, because the sum `Σ_{i≤k} (B k + C)(T/S)ⁱ` is `≤ (Bk + C)/(1 − T/S)`); hence the
series `Σ aₖ tᵏ` converges on `|t| < 1/S` and defines an analytic `y`.  Finally check the
coefficient identity (Cauchy product of the two series, derivative of a `tsum` of a power
series: `Mathlib.Analysis.Calculus.SmoothSeries.deriv_tsum`,
`Commons.Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound`) and conclude that the
function `y` satisfies `θ²y = b·θy + c·y` on the disc of convergence by the uniqueness of the
coefficients.

### 2. `Work.C17f.xs_factor_data` (the algebraic data at `x_s`)

With `xsC a b = ((xs a b : ℝ) : ℂ)` and `Q2x a b = (X − 1/x_s)(X−1)X(X+1)(X² − ledC·X + 1)`
(module `Submission.Work.C17.logP_local_defs`):

* `P2x = (X − x_s)·Q2x` over `ℂ`;
* `Q2x(x_s) = P1x(x_s) = P2x'(x_s) ≠ 0` (from `Work.C17.local_exp_data`, `led_factor`,
  `led_real_data`; `x_s` is the root of the `ledD`-quadratic, `x_s + 1/x_s = ledD`);
* `P1x − P1x(x_s)` is divisible by `(X − x_s)` in `ℂ[X]`; the quotient `S` is the `r̃` of the
  θ-form above.

This is a computation on explicit polynomials plus the elementary real facts
`0 < x_s < 1` (`Work.C17.xs_pos_and_sq_lt_one`) and `x_s + 1/x_s = ledD`.

### 3. `Work.C17f.Pfun_solves_M` (transfer of `logP_ode` to functions)

`Work.C17.logP_ode` (`Submission.CDT.LogMIdentities`) is the *coefficient-wise* identity
`M(P) = r_a·RaFam + r_b·RbFam + r_{ab}·RabFam`, whose right hand side is the polynomial
`rhoMx a b ra rb rab` (degree ≤ 4).  Lemma 3 is its function-level form on the disc of
convergence: from `hconv` (the series of `Submission.CDT.logP` sums to `Pfun`) deduce

```
P2x(z)·(Pfun)'' (z) + P1x(z)·(Pfun)'(z) + P0x(z)·Pfun z = (rhoMx a b ra rb rab)(z)
```

for `‖z‖ < x_s`.  Route: unfold `Pfun` as a `tsum` of a power series, use the standard facts
that the derivative of such a `tsum` is the derived series and that products are Cauchy
products (all available in Mathlib, e.g. `deriv_tsum`), and compare coefficients with
`logPAODE_eq`/`coe_P2x`/`coe_P1x`/`coe_P0x` (`Work.C17.seventeen_indep`).

## How the three pieces are assembled (this part is done by the requester)

Given `y₁` from piece 1 (with `a₀ = 1`), piece 3 to know that `Pfun` solves the inhomogeneous
equation on `Ω = ball(x_s,δ) ∩ ball(0,x_s)` and piece 2 for the data at `x_s`, one writes
`w = Pfun/y₁` on `Ω` and `ζ = w'`.  With `B := ball(x_s,δ)`, `q := Q2x`, `S` as in piece 2 and
`g := −y₁^{-2}·exp(−∫ S/q)` (an antiderivative on the convex ball `B`), the function
`ζ_h = g/(z − x_s)` solves the homogeneous first order equation
`ζ' + (1/(z−x_s) + 2y₁'/y₁ + S/q)ζ = 0`, while
`ζ_p = g·dslope ℓ x_s` with `ℓ` an antiderivative of `G/(q·y₁·g)` vanishing at `x_s` solves the
inhomogeneous equation `ζ' + A ζ = G/(P2x·y₁)` on `Ω`;  hence `ζ = ζ_p + c·ζ_h` on `Ω` for a
constant `c` (Ω is convex), so `w' = g·(ℓ + c)/(z − x_s)` on `Ω`.  Setting `κ := g(x_s)·c`
and `L := g·(ℓ + c)` one has `w' − κ/(z − x_s) = dslope L x_s` on `Ω`; this is the derivative
of an analytic function `W₀` on `B`, and `w − κ·log(x_s − ·) − W₀` is constant on `Ω`.  Hence
`Pfun = κ·y₁·log(x_s − ·) + y₁·(W₀ + C)` on `Ω` with `κ ≠ 0` (otherwise `Pfun` would extend
holomorphically to `B`, contradicting `hnot`).
-/

namespace Work.C17

end Work.C17
