import Mathlib
import Submission.Commons.Data.Nat.Choose.centralBinom_convolution
import Submission.Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul_pow
import Submission.Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul
import Submission.Commons.Analysis.Complex.sq_sqrt_of_slitPlane
import Submission.Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane
import Submission.Commons.Analysis.Complex.sqrt_ofReal_of_nonneg
import Submission.Commons.Analysis.Complex.cpow_neg_half_eq_inv_sqrt
import Submission.Commons.Analysis.Analytic.even_analytic_factor_sq
import Submission.Commons.Analysis.Analytic.even_analytic_factor_sq_onBall
import Submission.Commons.Analysis.Complex.sqrt_analyticAt
import Submission.Commons.Analysis.Analytic.coeff_growth_of_analyticAt
import Submission.Commons.Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound
import Submission.Commons.Analysis.InfiniteSum.powSeries_product_hasSum_of_abs_summable
import Submission.Commons.Analysis.InfiniteSum.hasSum_pow_eq_zero_of_eventually_zero
import Submission.Commons.Analysis.Analytic.complex_coeff_eq_ofReal_axis
import Submission.Commons.Analysis.InfiniteSum.powSeries_product_hasSum_of_abs_summable_complex
import Submission.Commons.Analysis.Complex.cauchy_coeff_bound

/-!
# The Beukers generating series of the logarithm (first brick of CDT)

This module begins the formalization of the analytic objects behind
**Theorem C** (`logsmain`) of Calegari–Dimitrov–Tang, *The linear
independence of 1, ζ(2), and L(2,χ₋₃)*, arXiv:2408.15403 — the
irrationality of `log(1+1/m)·log(1+1/n)` and the linear independence of
`1, log(1+1/m), log(1+1/n), log(1+1/m)·log(1+1/n)`.

The proof of Theorem C (§"Products of two logarithms" of the paper) works
with the *Apéry-limit* generating series of the logarithm function.  The
very first object it constructs is the **Beukers function**

`A(a,x) = (1 − 2a·x + x²)^(−1/2) = Σ_{n≥0} u_n(a)·x^n`   (paper eq. (beukersA)),

whose coefficients are the Legendre-type numbers `u_n(a)`; the paper
records two immediate facts: `A(a,x) ∈ ℤ[[x]]` for odd `a` (and in
`ℤ[[x/2]]` otherwise), and the first-order ODE

`(1 − 2a·x + x²)·y′ + (x − a)·y = 0`   (paper eq. (odeone)).

This module provides that definition and the first lemmas making it
usable (all formal, zero axioms):

* `beukersU` — the coefficients `u_n(a)`, defined by the 3-term recurrence
  `u_0 = 1`, `u_1 = a`, `(n+2)u_{n+2} = (2n+3)a·u_{n+1} − (n+1)u_n`
  (equivalently `(n+1)u_{n+1} = (2n+1)a·u_n − n·u_{n−1}` for `n ≥ 1`);
* `beukersA` — the formal power series `A(a,x) = Σ u_n(a) x^n`;
* `beukersU_step` — the stepping relation (the arithmetic lemma all
  downstream coefficient computations use);
* initial values `u_0 = 1`, `u_1 = a`, `u_2 = (3a²−1)/2`
  (`beukersA_coeff_zero/one/two`);
* `beukersA_ode` — the first-order ODE of the paper (eq. (odeone)) as an
  identity of formal power series (proved coefficient-wise from the
  recurrence in `beukersA_ode_coeff`).

Later sections add the rest of the analytic spine of the Apéry-limit method
(see the section headers for the full inventory):
* parity `u_n(-a) = (-1)^n u_n(a)`, `v_n(-a) = (-1)^{n+1} v_n(a)`
  (`beukersU_neg_mul`/`beukersV_neg_mul`) and the induced sign flip of the
  ratio `beukers_ratio_neg` — the reduction of every negative parameter to
  `|a| ≥ 3`;
* the **real convergence** of the Apéry tail: termwise geometric bounds
  (`beukersU_recip_le_real`, `beukers_geom_bound`), summability of
  `Σ_k 1/(k·uₖ·uₖ₋₁)` for `a ≥ 3` (`beukersUV_series_summable`,
  `beukersTail4_summable`), the real telescoping identity
  (`beukersUV_real_telescope`), and the convergence of the Apéry ratio
  sequence `v_N/u_N` in `ℝ` (`beukersUV_apéry_tendsto`).  The
  identification of the limit with `½·log((a+1)/(a−1))` (paper
  eq. (beukerslimit)) is the next analytic brick.

The logsmain application later sets `a = 1 + 2m` (odd), so that
`log(1+1/m) = log((a+1)/(a−1))` is the Apéry limit `lim v_n(a)/u_n(a)`
with `v_n` the coefficients of the companion function
`H(a,x) = A(a,x)·∫₀ˣ dt/A(a,t)` — **both series live in this module**
(`beukersV`/`beukersH`, §"The companion series" below) — and
`A(a,x) ∈ ℤ[[x]]` for odd `a`.

## Roadmap (status of the algebraic/analytic bricks, updated)

**Done in this module** (all fully proved, no axioms):

1. **`A(a,x)²·Q = 1`** (`beukersA_sq_mul`, from the first-order ODE via
   the Leibniz rule): `A` is the formal inverse square root of
   `Q = 1 − 2aX + X²`.
2. **Structural decomposition** (`beukersA_eq_beukersG`):
   `A = (1−aX)^(−1)·S(Z)` with `Z = (a²−1)X²(1−aX)^(−2)` and
   `S` the inverse-square-root series `S²(1−X) = 1`
   (`beukersQ/W/Z/T/G`, `centralSqrtSeries_subst_sq_mul`,
   `beukersQ_eq`, `beukersG_sq_mul`).
3. **Binomial closed form** (`beukersU_closed`):
   `u_n(a) = Σ_{2j≤n} C(2j,j)·C(n,2j)·a^{n−2j}·((a²−1)/4)^j`
   (route: coefficient extraction of `W·(S∘Z)` through the truncation
   `beukersT_coeff_eq_trunc` / `coeff_beukersG_eq_coeff_W_mul_trunc` /
   `coeff_beukersW_mul_trunc`; uses the Commons coefficient formula for
   `(1−aX)^(−e)`, `coeff_inv_one_sub_C_mul_pow`).
4. **Integrality** (`beukersU_int_of_odd`): for odd integer `a`,
   `u_n(a) ∈ ℤ` (`A(a,x) ∈ ℤ[[x]]` for odd `a`), via
   `exists_int_sq_sub_one_div_four` (`(a²−1)/4 = k(k+1)` for `a = 2k+1`).
5. **Companion identity** (`beukersH_eq_A_mul_int`): the companion
   `H` (coefficients `v_n`) equals `A·W` where `W = ∫₀ˣA` is the formal
   antiderivative (`beukersInt`, `beukersInt_derivative`).  Proof: both
   solve the inhomogeneous ODE `Q·y′+(X−a)y = 1` with zero constant term;
   the needed uniqueness is `ode_homogeneous_eq_zero_of_zero`, built on the
   coefficient identities `coeff_ode_hom_zero`/`coeff_ode_hom_succ`.

6. **Coefficient read-off** (`beukersV_eq_sum`, `beukersV_eq_sum_aux`):
   `v_n(a) = Σ_{j=1}^{n} u_{n−j}(a)·u_{j−1}(a)/j`, from `H = A·W` via the
   coefficient-of-product convolution (antidiagonal → range reindexing;
   the `k = n` term vanishes because `w_0 = 0`).
7. **Denominator claim** (`beukersV_lcm_int_of_odd`,
   `beukersV_lcm_term_int`): for odd integer `a`, `[1,…,n]·v_n(a) ∈ ℤ`,
   where `[1,…,n] = lcm {1,…,n}` — each read-off summand
   `L·u_{n−j}·u_{j−1}/j = (L/j)·u_{n−j}·u_{j−1}` is a product of
   integers (`j ∣ L` by `Finset.dvd_lcm`, `u_k ∈ ℤ` by
   `beukersU_int_of_odd`), summed by `Int.cast_sum`.

8. **Assembly** (`beukers_coeff_arithmetic`): joint statement of the
   coefficient arithmetic of eq. (beukersB) — `u_n(a) ∈ ℤ` and
   `[1,…,n]·v_n(a) ∈ ℤ` for odd `a`, every `n`.

**Remaining bricks** (next sessions):

* **the analytic identification of the Apéry limit**
  `lim_n v_n/u_n = ½·log((a+1)/(a−1))` (paper eq. (beukerslimit)).  Precise
  route (from the paper's eq. (beukersB)/(beukerslimit) mechanism):
  — write `ρ = a−√(a²−1)` (the smallest positive singularity of
    `A(a,x) = (1−2ax+x²)^(−1/2)`), `η_a = ½·ln((a+1)/(a−1))`;
  — establish the real/formal identity
    `H(a,x) − η_a·A(a,x) = A(a,x)·∫_ρ^x dt/√(1−2at+t²)` (paper eq.
    (beukersB)); the RHS *overconverges* at `x = ρ` (the `√`-monodromy of
    `A` and of the integral cancel), i.e. `Σ_n (v_n − η_a u_n) x^n` has
    radius of convergence `> 1/a` (next singularity `1/ρ = a+√(a²−1)`);
  — with `u_n ≥ a^n` (`beukersU_lower_bound`) and the coefficient bound
    `|v_n − η_a u_n| ≤ C·r^(−n)` for any `1/a < r < a+√(a²−1)` (Cauchy),
    the ratio `(v_n − η_a u_n)/u_n = O((ar)^(−n)) → 0`.
  **Committed so far** (the real anchor, §"The real analytic companion"):
  the closed-form antiderivative `W(a,x)` of `A(a,x) = 1/√(1−2ax+x²)` with
  `W(0) = 0`, its boundary value `W(a,ρ_a) = η_a` (`beukersWReal_rho_eq_eta`
  — the arithmetic content of the paper identity), the derivative
  `W′ = A` on `(−∞, ρ_a)` (`beukersWReal_hasDerivAt`) and the FTC
  `W(x) = ∫₀ˣ A` (`beukersWReal_eq_integral`), plus the closed-form
  functional identity `H − η_a A = A·(W − W(ρ_a))`
  (`beukers_apéry_closed_form`).
  **Committed so far** (the complex chapter's first coordinate,
  §"The complex quadratic Q(z) = (1−ρz)(1−rz)"): the complexified
  quadratic `beukersQuadC` with its roots `ρ_a` and `r_a = 1/ρ_a`, the
  factorizations `Q(z) = (1−ρz)(1−rz) = (z−ρ)(z−r)`, the root
  characterization `Q(z)=0 ↔ z=ρ ∨ z=r`, nonvanishing of `Q` on the disc
  `|z| < ρ`, the derivative/simple-root-at-`ρ` and continuity facts, and —
  the seed of the continuation — the square-root coordinate
  `Q(ρ−u²) = u²·(2c+u²)`, `c = √(a²−1)`, whose factor `2c+u²` is nonzero
  on a small disc (`beukers_rho_pull_factor_ne_zero`).
  **Committed so far** (§"The local branch of √Q in the square-root
  coordinate"): the local branch objects `B(u) = √(2c+u²)` and
  `σ(u) = u·B(u)` with their differentiability/continuity on the small
  disc, membership `2c+u² ∈ Complex.slitPlane` there, the square laws
  `B(u)² = 2c+u²` and `σ(u)² = Q(ρ−u²)`, and `B(0) = √(2c) ≠ 0`.
  **Committed so far** (§"The u-coordinate derivative of the companion
  antiderivative"): the real derivative identity `d/du W(ρ−u²) = −2/B(u)`,
  `B(u) = √(2c+u²)` (`beukersWReal_rho_sub_sq_hasDerivAt`/`_deriv`, from
  `W′ = A`, the real pullback `Q(ρ−u²) = u²(2c+u²)`, and
  `A(ρ−u²) = 1/(u·B(u))` on `u > 0`), with the sign/monodromy analysis
  recorded for the complex lift.
  **Committed so far** (§"The complex lift of the companion antiderivative
  W"): the principal-branch lifts `Wℂ(z) = Complex.log((a+1)/(a−z+√Q(z)))`
  (`beukersWComplex`) and `Aℂ(z) = 1/√Q(z)` (`beukersAComplex`), and the
  real-axis agreements `beukersWComplex_eq_ofReal`,
  `beukersAComplex_eq_ofReal` (`Wℂ(↑x) = ↑(W(a,x))`,
  `Aℂ(↑x) = ↑(A(a,x))` for `x < ρ` — the branch matches the real theory on
  `[0, ρ)`).
  **Committed so far** (§"The domain of holomorphy and Wℂ′ = Aℂ"): the
  domain `beukersWComplexDomain a = {z | Q(z) ∈ slitPlane ∧
  (a+1)/(a−z+√Q(z)) ∈ slitPlane}`, its containment of the real interval
  `(−∞, ρ)` (`beukersWComplexDomain_ofReal`), the derivatives of `√Q`
  (`beukersQuadC_sqrt_hasDerivAt`, value `Q′/(2√Q)`) and of the
  denominator (`beukersDenomC_hasDerivAt`), and the chain identity
  **`beukersWComplex_hasDerivAt : Wℂ′ = Aℂ` on the domain**.
  **Committed so far** (§"The u-coordinate expansion of A·(W−η_a) (real
  axis)"): `W` continuous at `ρ` (`beukersWReal_continuousAt_rho`), the
  FTC identity `W(ρ−u²) − η = −∫₀^u 2/B` (`beukersWReal_rho_sub_sq_eq_int`),
  and the boundary value `A(ρ−u²)·(W(ρ−u²) − η) → −1/√(a²−1)` as `u → 0⁺`
  (`beukers_apéry_rho_sub_sq_tendsto`) — the even-extension value in `u`
  (`u² = ρ−z`).
  **Committed so far** (§"The square-root coordinate σ(u) at ρ (complex,
  aligned)"): `B(u) = √(2c+u²)` even (`beukersSqrtC_neg`), `σ(u) = u·B(u)`
  odd (`beukersSigma_neg`), and the **alignment**
  `beukersSigma_eq_sqrt_of_principal`: for real `u > 0`, `σ(u)` equals the
  principal `Complex.sqrt` of `Q(ρ−u²)` — the positive determination of the
  real theory, so `A(z(u)) = 1/σ(u)` there.
  **Committed so far** (§"Toward the even extension G(u)"): `z(−u) = z(u)`
  (`beukers_zC_even`) and the pullback parity lemmas
  (`beukersWComplex_pull_even`, `beukersAComplex_pull_even`,
  `beukers_apéry_pull_real_even`), the real-vs-complex regular factor
  (`beukersSqrtC_ofReal_eq`), and **`A` through `σ`**
  (`beukersAComplex_eq_sigma_inv`: `Aℂ(z(u)) = 1/σ(u)` for real `u > 0`).
  **Committed so far** (§"The analytic continuation: primitive of the
  holomorphic −2/B"): **`beukers_neg2B_primitive_on_ball`** — by Morera
  (`DifferentiableOn.isExactOn_ball` + `Complex.IsExactOn.with_val_at`)
  there is a holomorphic `H` with `H(0) = 0` and `H′(u) = −2/B(u)` on the
  disc `‖u‖ < √(2·√(a²−1))` — the `u`-coordinate antiderivative that
  extends `u ↦ W(ρ−u²) − η` off the real axis.
  **Committed so far** (§"The odd antiderivative HU and the even extension
  candidate G"): the odd-symmetrized antiderivative
  `HU(u) = (P(u) − P(−u))/2` (`beukersHU`: odd `beukersHU_neg`,
  `beukersHU_zero`, from the chosen Morera primitive `beukersH0`), the even
  extension candidate `G(u) = HU(u)/σ(u)` (`beukersGExt`, even on the
  punctured coordinate disc by `beukersGExt_neg`), and — via the
  `deriv`-based route (`deriv_comp`, `deriv_sub`, `deriv_div_const`,
  `HasDerivAt.deriv`, `deriv_neg`) — **`beukersHU_deriv : HU′ = −2/B`** on
  the coordinate disc.
  **Committed so far** (§"Real-axis restriction of HU (the agreement
  normalization)"): `beukersHU_differentiableAt`, `beukersSqrtC_ofReal_neg2`
  (`−2/B(↑t) = ↑(−2/B(t))`), and **`beukersHU_real_deriv`** — for real
  `0 < u < √(2c)`, `HasDerivAt (fun t => HU(↑t)) (−2/B(u)) u`, via
  `HasDerivAt.comp_ofReal` (`Mathlib/Analysis/Complex/RealDeriv.lean`):
  the normalization making the real-axis agreement
  `HU(u) = W(ρ−u²) − η` true.  **`beukersHU_restrict_cont_at`** (per-point
  continuity on the disc) and **`beukersHU_real_axis`** (the real-FTC
  agreement, same shape as `beukersWReal_rho_sub_sq_eq_int`: both sides
  vanish at 0, both restricted derivatives are `−2/B`, so the difference
  is constant 0) are now COMMITTED.
  **Committed so far** (§"The even holomorphic extension G of
  A·(W−η_a)∘z(u) through u = 0"): the real-axis agreement
  `beukersGExt_real_axis` (`G(↑u) = ↑(A(ρ−u²)·(W(ρ−u²) − η_a))` for
  `0 < u < √(2c)`), the real-axis boundary value
  `beukersGExt_real_axis_tendsto` (`G(↑u) → ↑(−1/√(a²−1))` as `u → 0⁺`),
  the full two-sided boundary value `beukersGExt_tendsto_zero`
  (`G(u) → ↑(−1/√(a²−1))` as `u → 0`, `u ≠ 0`: `G = (HU/u)·B⁻¹`,
  `HU/u → HU′(0) = −2/B(0)`, `B(u) → B(0)`, `B(0)² = 2√(a²−1)`), and
  complex differentiability `beukersGExt_differentiableAt` at every
  `u ≠ 0` of the coordinate disc.  Together with the punctured-disc
  evenness `beukersGExt_neg` this is the even holomorphic extension
  through `u = 0` (`x = ρ`) with value `−1/√(a²−1)`.
  **Committed so far** (§"G0: the even holomorphic extension through u = 0"):
  the redefinition `G0 = update G 0 ↑(−1/√(a²−1))` is analytic at `0`
  (`beukersGExt0_analyticAt_zero`, removable singularity via
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  with the two-sided limit `beukersGExt_tendsto_zero`), takes the boundary
  value at `0` (`beukersGExt0_zero`), is even on the whole coordinate disc
  (`beukersGExt0_even`), and is complex-differentiable on the whole
  coordinate disc (`beukersGExt0_differentiableOn`) — the **even
  holomorphic extension of `A·(W−η_a)∘z(u)` through `u = 0`** (value
  `−1/√(a²−1)`; in the `z`-plane through `x = ρ`).
  **Committed so far** (§"G0 as a named function, and the descent through
  `u = 0` to `w = u²`"): the named extension `beukersG0`
  (`beukersG0_zero`, `beukersG0_eq_GExt`, `beukersG0_analyticAt_zero`,
  `beukersG0_even`, `beukersG0_differentiableOn`, `beukersG0_real_axis`,
  `beukersG0_even_eventually`), the **descent** `beukersG0_descends_sq`
  — brick A4 (existence form): `∃ F`, `F` analytic at `0` with
  `F (u²) = G0(u)` near `u = 0`, `F 0 = −1/√(a²−1)` — via the Commons
  lemma `Commons.Analysis.Analytic.even_analytic_factor_sq` (even analytic
  functions factor through the square map), and the real-axis consequence
  `beukersF_real_axis`: for small real `t > 0`,
  `F (↑t) = ↑(A(ρ−t)·(W(ρ−t)−η_a))` (the `x`-plane read `x = ρ−t` below
  the singularity `ρ`).
  **Committed so far** (the ball form of the descent and the elementary
  radius inequalities): the quantitative descent `beukersG0_descends_sq_onBall`
  — for every `R0 < R_u = √(2√(a²−1))` there is `F` with
  `HasFPowerSeriesOnBall F q 0 (↑R0)²`, `F 0 = −1/√(a²−1)` and
  `F (u²) = G0(u)` for all `‖u‖ < R0` — via the Commons lemma
  `Commons.Analysis.Analytic.even_analytic_factor_sq_onBall` (fed with the
  closed-ball power series of `G0` from
  `DifferentiableOn.hasFPowerSeriesOnBall`); and the real inequalities
  `beukers_cont_radius_gt_one_div` / `beukers_rho_add_one_div_lt_two_sqrt`
  (`1/a < 2√(a²−1) − ρ_a`, i.e. the `w`-disc of radius `2√(a²−1)` around the
  continuation point leaves room for a Cauchy circle at `x = 0` of radius
  bigger than `1/a`).
  **Committed so far** (§"Analyticity at `0` of the complex lifts and of the
  real companion functions (A5, stage 1)"): holomorphy at `0` of the
  complex lifts `beukersAComplex`/`beukersWComplex`
  (`beukersAComplex_analyticAt_zero`, `beukersWComplex_analyticAt_zero`, via
  `Commons.Analysis.Complex.sqrt_analyticAt` and `analyticAt_clog`) with
  values `beukersAComplex_zero` (=1), `beukersWComplex_denom_zero`/
  `_arg_zero` (log argument = 1), and the **real-analyticity at `0` of the
  companion functions** `beukersAReal_analyticAt_zero`,
  `beukersWReal_analyticAt_zero` (via `AnalyticAt.re_ofReal` + the real-axis
  agreements).
  **Committed so far** (§"A5 stage 2 — the coefficient bridge", the real
  axis): the first-order ODE for `A` (`beukersAReal_hasDerivAt`,
  `beukersAReal_ode_eventually`), the iterated-derivative 3-term recurrence
  at `0` (`beukersAReal_iterDeriv_step_all`, via the Leibniz expansion
  `iteratedDeriv_quadratic_mul_zero` of polynomial products), the real
  coefficient sequence `beukersUR` (`beukersUR_eq_cast` = the cast of the
  rational `beukersU`), **`beukersAReal_iterDeriv_eq_fact`**
  (`A^{(n)}(0) = n!·u_n(a)`), and the analytic identity
  `beukersAReal_hasSum_series`: near `0`,
  `A(a,x) = Σₙ u_n(a)·xⁿ`.  The `W`-side: `W′ = A` gives
  `beukersWReal_iterDeriv_succ`/`_eq` (`W^{(n)}(0) = n!·wₙ`, `w₀ = 0`,
  `wₙ = u_{n−1}/n`) and `beukersWReal_hasSum_series`.
  **Committed so far** (§"A5 stage 2 (cont.) — the `H = A·W` coefficient
  half"): the power-series product machinery
  (Commons `Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound`,
  `...powSeries_product_hasSum_of_abs_summable`), the geometric growth of the
  coefficients (`beukersUR_growth`, `beukersWSeq_growth`) and the absolute
  summability near `0` (`beukersAReal_series_abs_summable`,
  `beukersWSeq_series_abs_summable`), the real companion coefficients
  `beukersVR` (`beukersVR_eq_range_conv` = the convolution, `beukersVR_eq_cast`
  = the cast of the rational `beukersV`), and **`beukersH_hasSum_series`**:
  near `0`, `A(a,x)·W(a,x) = Σₙ v_n(a)·xⁿ`, and
  **`beukers_hasSum_apéry_series`**: `A·(W−η_a) = Σₙ (v_n(a)−η_a·u_n(a))·xⁿ`.
  **Committed so far** (§"A5 stage 2 (cont.) — the complex-lift
  identification"): the generic real-axis lifting lemma
  `Commons.Analysis.Analytic.complex_coeff_eq_ofReal_axis` (complex Taylor coefficients of a
  holomorphic function agreeing with a real-analytic function on the real
  axis equal the casts of the real Taylor coefficients), and its applications
  `beukersAComplex_coeff_eq` (Taylor coefficients of `Aℂ` at `0` are
  `u_n(a)`) and `beukersWComplex_coeff_eq` (those of `Wℂ` are `wₙ`).
  **Committed so far** (§"A5 stage 2 (cont.) — the complex product"):
  `beukersAComplex_hasSum_series` / `beukersWComplex_hasSum_series` (the
  holomorphic power series of `Aℂ`, `Wℂ` at `0`), their absolute summability
  on a disc, `beukersVR_conv_cast_eq` (convolution of the cast coefficients =
  cast of `v_n(a)`), and **`beukersAComplexWComplex_hasSum_series`** /
  **`beukers_hasSum_apéry_complex`**: near complex `0`,
  `Aℂ·(Wℂ−η_a) = Σₙ (v_n(a) − η_a·u_n(a))·zⁿ`.
  **Committed so far** (§"A6 — opening"): the complex companion product
  `Hℂ(z) = Aℂ(z)·(Wℂ(z)−η_a)` (`beukersHComplex`), holomorphic at `0` with
  power series `Σ (v_n−η_a·u_n)zⁿ` (`beukersHComplex_analyticAt_zero`,
  `beukersHComplex_hasSum_series`), its real-axis agreement with the real
  companion (`beukersHComplex_eq_ofReal`, `beukers_apéry_realAxis_equality`),
  and the **real-axis power series of `Hℂ`**
  (`beukersHComplex_hasSum_series_realAxis`: for real `x` near `0`,
  `Hℂ(↑x) = Σ ((v_n−η_a·u_n):ℂ)·(↑x)ⁿ`) — the coefficient sequence is now
  identified with the power series of both the real companion and the
  restricted `Hℂ` on a common interval around `0`.
  **Committed so far** (§"A6 — continuation (first stone)"): holomorphy of
  `Aℂ`/`Wℂ`/`Hℂ` at every point of the interval below `ρ`
  (`beukersAComplex_analyticAt_of_slitPlane`,
  `beukersWComplex_analyticAt_of_domain`,
  `beukersHComplex_analyticAt_of_domain`,
  `beukersHComplex_analyticAt_ofReal_lt`) and the **overlap with the
  descent**: `beukers_continuation_overlap` — for a descended `F`,
  `F(↑t) = Hℂ(↑(ρ−t))` on a real segment just below `ρ` (the two anchored
  ends of the continuation agree).
  **Committed so far** (§"A6 — global (germ gluing along the continuation
  interval)"): the real companion `G_a(x) = A(x)·W(x) − η_a·A(x)`
  (`beukersRealApéry`, `beukersRealApéry_eq`) is real-analytic at every real
  point below `ρ` (`beukersRealApéry_analyticAt`), agrees with the restricted
  `Hℂ` on a whole real neighbourhood of each such point
  (`beukersHComplex_eq_ofReal_eventually`), and the bundled gluing lemma
  `beukers_apéry_germ_glue` records at each `x₀ < ρ` the triple
  (Hℂ-analytic at `↑x₀`, `G_a`-analytic at `x₀`, axis-agreement near `x₀`) —
  the germs along `(0, ρ)` are coherent lifts of the single real-analytic
  `G_a`.
  **Committed so far** (§"A6 — assembly (the `ρ`-extension of the
  continuation)"): for a descended `F`, the candidate continuation
  `g(z) = F(ρ−z)` (`beukersApéryRhoExt`) is holomorphic at `ρ`
  (`beukersApéryRhoExt_analyticAt_rho`), equals `Hℂ` on the real axis just
  below `ρ` (`beukersApéryRhoExt_eq_HComplex_below`), and the bundle
  `beukers_apéry_rho_extension` records both — `g` continues the companion
  product through the singularity.
  **Committed so far** (§"A6 — the real-axis bridge of the `ρ`-extension"):
  the pointwise engine `beukers_apéry_rho_extension_interval_gen` — for a
  descended `F`, `g(z) = F(ρ−z)` equals the companion `Hℂ` at every real
  `x < ρ` whose distance `w = ρ − x` fits the coordinate discs (`w < R0²`,
  `w < 2√(a²−1)`), proved pointwise through the `u = √w` coordinate — its
  interval form `beukers_apéry_rho_extension_interval` (all of `(0, ρ)` when
  `ρ < R0²`), the two-sided eventual form
  `beukers_apéry_rho_extension_realAxis_eventually`, and the elementary
  radius comparisons `beukers_rho_lt_two_sqrt`,
  `beukers_rho_add_one_lt_two_sqrt` and the descent-radius existence
  `beukers_exists_descend_R0` (`ρ_a + 1 < R0² < 2√(a²−1)`).
  **Committed so far** (§"A6 — holomorphy of the `ρ`-extension at `0` and
  the germ equality"): `g` holomorphic at `0` and on the whole unit disc
  (`beukersApéryRhoExt_analyticAt_zero`,
  `beukersApéryRhoExt_analyticAt_of_unitBall`, from `F`'s power series on
  `|w| < R0²` with `R0² > ρ + 1`); the **germ equality**
  `beukers_apéry_g_eq_HComplex_eventually` (`g = Hℂ` on a whole complex
  neighbourhood of `0` — both holomorphic at `0` and equal on `(0, ρ)`, by
  the principle of isolated zeros); and the power-series consequences
  `beukers_apéry_g_hasSum_series` / `beukers_apéry_g_hasFPowerSeriesAt`:
  `g` is represented near `0` by the companion series
  `Σ(v_n − η_a·u_n)·zⁿ`.
  **Committed so far** (§"A6 — assembly: the geometric coefficient bound"):
  **`beukers_apéry_coeff_growth`** — there are `C > 0`, `r > 1/a` with
  `‖(v_n(a) − η_a·u_n(a) : ℂ)‖ ≤ C / rⁿ` for every `n`: the companion power
  series overconverges past `ρ_a` (the `ρ`-extension carries it onto the unit
  disc) and the Cauchy estimate on the circle of radius
  `(1/a + 1)/2 ∈ (1/a, 1)` gives the geometric decay.
  **Committed so far** (§"A7 — the Apéry limit"): the real-parameter
  positivity/lower bound `beukersUR_pos`, `beukersUR_lower_bound`
  (`u_n ≥ aⁿ`), and **`beukers_apéry_limit`**: for real `a ≥ 3`,
  `v_N(a)/u_N(a) → η_a = ½·log((a+1)/(a−1))` as `N → ∞` (paper
  eq. (beukerslimit)) — from `|v_N/u_N − η_a| ≤ C·(a·r)^{−N} → 0`.
  **DONE later in this module / chapter**: the rational-parameter
  restatement of the Apéry limit for odd `ã = 1 + 2m`
  (`beukers_apéry_limit_rat`, §A7 below) and the Hadamard-product
  machinery (`P_A = A(a,x)⋆A(b,x)`, the product ODE of the paper eq.
  (ODE) and the beyond-cusp overconvergence of the `P`-family) — see the
  A7 sections below and module `Submission.CDT.LogHadamard`.
-/

open scoped BigOperators
open scoped ENNReal NNReal
open PowerSeries
noncomputable section

namespace Submission.CDT

/-- `u_n(a)`: the coefficients of the Beukers generating series
`A(a,x) = (1 - 2a·x + x²)^(-1/2) = Σ u_n(a)·x^n`, defined here via the
3-term recurrence `u_0 = 1`, `u_1 = a`,
`(n+2)·u_{n+2} = (2n+3)·a·u_{n+1} − (n+1)·u_n`. -/
def beukersU (a : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => a
  | n + 2 =>
      (((2 * (n : ℚ)) + 3) * a * beukersU a (n + 1) - ((n : ℚ) + 1) * beukersU a n) /
        ((n : ℚ) + 2)

/-- the Beukers generating series `A(a,x) = Σ_{n} u_n(a)·x^n ∈ ℚ⟦x⟧`. -/
def beukersA (a : ℚ) : PowerSeries ℚ := PowerSeries.mk (beukersU a)

lemma beukersU_zero (a : ℚ) : beukersU a 0 = 1 := rfl

lemma beukersU_one (a : ℚ) : beukersU a 1 = a := rfl

/-- coefficient of `beukersA` is `beukersU`. -/
lemma beukersA_coeff (a : ℚ) (n : ℕ) : PowerSeries.coeff n (beukersA a) = beukersU a n := by
  rw [beukersA, PowerSeries.coeff_mk]

/-- the 3-term stepping relation for the coefficients (the paper's
recurrence behind eq. (odeone); all downstream coefficient arithmetic
rests on this). -/
lemma beukersU_step (a : ℚ) (n : ℕ) :
    ((n : ℚ) + 2) * beukersU a (n + 2) =
      ((2 * (n : ℚ)) + 3) * a * beukersU a (n + 1) - ((n : ℚ) + 1) * beukersU a n := by
  simp [beukersU]
  field_simp

lemma beukersA_coeff_zero (a : ℚ) : PowerSeries.coeff 0 (beukersA a) = 1 := by
  rw [beukersA_coeff, beukersU_zero]

lemma beukersA_coeff_one (a : ℚ) : PowerSeries.coeff 1 (beukersA a) = a := by
  rw [beukersA_coeff, beukersU_one]

lemma beukersU_two (a : ℚ) : beukersU a 2 = (3 * a ^ 2 - 1) / 2 := by
  have h := beukersU_step a 0
  norm_num at h
  rw [beukersU_one, beukersU_zero] at h
  rw [pow_two]
  nlinarith

lemma beukersA_coeff_two (a : ℚ) : PowerSeries.coeff 2 (beukersA a) = (3 * a ^ 2 - 1) / 2 := by
  rw [beukersA_coeff]
  exact beukersU_two a

/-- coefficient form of the first-order ODE (paper eq. (odeone)):
`(1 − 2a·X + X²)·A′ + (X − a)·A = 0`. -/
lemma beukersA_ode_coeff (a : ℚ) (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) *
        (PowerSeries.derivative (R := ℚ) (beukersA a)) + (X - C a) * beukersA a) = 0 := by
  classical
  let U : ℕ → ℚ := beukersU a
  have hU : ∀ m, PowerSeries.coeff m (beukersA a) = U m := by
    intro m
    exact beukersA_coeff a m
  have hU0 : U 0 = 1 := beukersU_zero a
  have hU1 : U 1 = a := beukersU_one a
  have hstep : ∀ m : ℕ, ((m : ℚ) + 2) * U (m + 2) =
      ((2 * (m : ℚ)) + 3) * a * U (m + 1) - ((m : ℚ) + 1) * U m := by
    intro m
    exact beukersU_step a m
  have hderiv : ∀ m, PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) (beukersA a)) = U (m + 1) * ((m : ℚ) + 1) := by
    intro m
    rw [PowerSeries.coeff_derivative, hU]
  have hsplit :
      ((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) * (PowerSeries.derivative (R := ℚ) (beukersA a))
        + (X - C a) * beukersA a
      = (PowerSeries.derivative (R := ℚ) (beukersA a)) - C (2 * a) * (X * PowerSeries.derivative (R := ℚ) (beukersA a))
        + X ^ 2 * (PowerSeries.derivative (R := ℚ) (beukersA a)) + X * beukersA a - C a * beukersA a := by
    ring
  rw [hsplit]
  simp only [map_add, map_sub, map_neg]
  let F : PowerSeries ℚ := beukersA a
  let dF : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (beukersA a)
  have hC2 : ∀ m : ℕ, PowerSeries.coeff m (C (2 * a) * (X * dF)) = (2 * a) * PowerSeries.coeff m (X * dF) := by
    intro m
    exact PowerSeries.coeff_C_mul m (X * dF) (2 * a)
  have hCa : ∀ m : ℕ, PowerSeries.coeff m (C a * F) = a * PowerSeries.coeff m F := by
    intro m
    exact PowerSeries.coeff_C_mul m F a
  have hXm : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 1) (X * g) = PowerSeries.coeff m g := by
    intro g m
    simpa using (PowerSeries.coeff_X_pow_mul g 1 m)
  have hX2m : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 2) (X ^ 2 * g) = PowerSeries.coeff m g := by
    intro g m
    exact PowerSeries.coeff_X_pow_mul g 2 m
  have hcoeff_dF : ∀ m : ℕ, PowerSeries.coeff m dF = U (m + 1) * (↑m + 1) := by
    intro m
    rw [show dF = PowerSeries.derivative (R := ℚ) (beukersA a) from rfl, hderiv m]
  have hcoeff_F : ∀ m : ℕ, PowerSeries.coeff m F = U m := by
    intro m
    rw [show F = beukersA a from rfl, hU m]
  cases n with
  | zero =>
      have hz1 : PowerSeries.coeff 0 (X * dF) = 0 := by simp
      have hz2 : PowerSeries.coeff 0 (X ^ 2 * dF) = 0 := by simp
      have hz3 : PowerSeries.coeff 0 (X * F) = 0 := by simp
      rw [hC2 0, hCa 0, hz1, hz2, hz3, hcoeff_dF 0, hcoeff_F 0]
      simp [hU0, hU1]
  | succ m =>
      cases m with
      | zero =>
          have hx1 : PowerSeries.coeff 1 (X * dF) = PowerSeries.coeff 0 dF := by
            simpa using (hXm dF 0)
          have hx2 : PowerSeries.coeff 1 (X ^ 2 * dF) = 0 := by
            simpa [pow_two, mul_assoc] using (hXm (X * dF) 0)
          have hx3 : PowerSeries.coeff 1 (X * F) = PowerSeries.coeff 0 F := by
            simpa using (hXm F 0)
          rw [hC2 1, hCa 1, hx1, hx2, hx3, hcoeff_dF 1, hcoeff_F 1]
          rw [hcoeff_dF 0, hcoeff_F 0]
          have h20 : ((0 : ℚ) + 2) * U (0 + 2) =
              ((2 * (0 : ℚ)) + 3) * a * U (0 + 1) - ((0 : ℚ) + 1) * U 0 := hstep 0
          ring_nf at h20 ⊢
          nlinarith [h20, hU0, hU1]
      | succ k =>
          have hx1 : PowerSeries.coeff (k + 2) (X * dF) = PowerSeries.coeff (k + 1) dF := by
            simpa [Nat.add_assoc] using (hXm dF (k + 1))
          have hx2 : PowerSeries.coeff (k + 2) (X ^ 2 * dF) = PowerSeries.coeff k dF := by
            exact hX2m dF k
          have hx3 : PowerSeries.coeff (k + 2) (X * F) = PowerSeries.coeff (k + 1) F := by
            simpa [Nat.add_assoc] using (hXm F (k + 1))
          rw [hC2 (k + 2), hCa (k + 2), hx1, hx2, hx3, hcoeff_dF (k + 2), hcoeff_F (k + 2)]
          rw [hcoeff_dF (k + 1), hcoeff_dF k, hcoeff_F (k + 1)]
          rw [show (k + 2) + 1 = k + 3 by omega, show (k + 1) + 1 = k + 2 by omega]
          have hs := hstep (k + 1)
          rw [show (k + 1) + 2 = k + 3 by omega, show (k + 1) + 1 = k + 2 by omega] at hs
          ring_nf at hs ⊢
          simp only [Nat.cast_add, Nat.cast_one] at hs ⊢
          linear_combination hs

/-- the first-order ODE of the paper (eq. (odeone)), as an identity of
formal power series: `(1 − 2a·X + X²)·A′ + (X − a)·A = 0`. -/
lemma beukersA_ode (a : ℚ) :
    ((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) * (PowerSeries.derivative (R := ℚ) (beukersA a))
      + (X - C a) * beukersA a = 0 := by
  apply PowerSeries.ext
  intro n
  exact beukersA_ode_coeff a n


/-! ## The Apéry companion series `H(a,x)` (inhomogeneous ODE with RHS `1`)

The companion of `A` used for the Apéry limit is the series
`H(a,x) = Σ v_n(a)·x^n` with `v_0 = 0`, the unique power series solving the
**inhomogeneous** first-order ODE

`(1 − 2a·X + X²)·H′ + (X − a)·H = 1`.

Analytically `H = A·∫₀ˣ A(t) dt` (`A(a,t) = (1−2at+t²)^(−1/2)`); its
coefficient equation forces `v₀ = 0`, `v₁ = 1`, and — since the right
hand side has only a constant term — the *homogeneous* recurrence
`(n+2)vₙ₊₂ = (2n+3)a·vₙ₊₁ − (n+1)vₙ` for **every** `n`, i.e. the *same*
second-order recurrence as `u`.  The Apéry limit of the pair is
`lim vₙ/uₙ = ∫₀^{x₀} A(t) dt = ½·log((a+1)/(a−1))`, `x₀ = a−√(a²−1)`
(the next bricks; the closed form already matches numerically: for
`a = 3`, `lim = ½ln2`).

> **Warning on the paper (arXiv 2408.15403, eq. (beukersB)).**  The paper's
> displayed formula writes `H(a,x) = (1/√(1−2ax+x²))·∫₀ˣ dt/√(1−2at+t²)`
> together with the expansion `x + a x²/2 + …` and claims the ODE above
> and the Apéry limit `½·log((a+1)/(a−1))` for the coefficients `vₙ` of
> that display.  Those three data are mutually inconsistent: the displayed
> integrand `dt/√(…)` gives the companion with the *different*
> inhomogeneous ODE `QH′+(X−a)H = Q` (`Q := 1−2aX+X²`), whose Apéry limit
> is `∫₀^{x₀}√Q dt = a/2 − ((a²−1)/2)·log((a+1)/(a−1))` (numerically
> `3/2−2ln2` at `a=3`), not the logarithm half.  This module follows the
> *consistent* companion above — `H = A·∫A`, ODE with RHS `1`, recurrence
> shared with `u` from `v₀=0`, `v₁=1` — which is the one the advertised
> log-limit and the logsmain application require.
-/

/-- `v_n(a)`: coefficients of the Apéry companion `H(a,x)`, defined by the
same homogeneous recurrence as `u`, with `v₀ = 0`, `v₁ = 1`:
`(n+2)vₙ₊₂ = (2n+3)a·vₙ₊₁ − (n+1)vₙ`. -/
def beukersV (a : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (((2 * (n : ℚ)) + 3) * a * beukersV a (n + 1) - ((n : ℚ) + 1) * beukersV a n) /
        ((n : ℚ) + 2)

/-- the Apéry companion series `H(a,x) = Σ v_n(a)·x^n ∈ ℚ⟦x⟧`. -/
def beukersH (a : ℚ) : PowerSeries ℚ := PowerSeries.mk (beukersV a)

lemma beukersV_zero (a : ℚ) : beukersV a 0 = 0 := rfl

lemma beukersV_one (a : ℚ) : beukersV a 1 = 1 := rfl

lemma beukersH_coeff (a : ℚ) (n : ℕ) : PowerSeries.coeff n (beukersH a) = beukersV a n := by
  rw [beukersH, PowerSeries.coeff_mk]

/-- the stepping relation for `v` — the homogeneous recurrence shared with
`u`, valid for every `n`. -/
lemma beukersV_step (a : ℚ) (n : ℕ) :
    ((n : ℚ) + 2) * beukersV a (n + 2) =
      ((2 * (n : ℚ)) + 3) * a * beukersV a (n + 1) - ((n : ℚ) + 1) * beukersV a n := by
  simp [beukersV]
  field_simp

lemma beukersV_two (a : ℚ) : beukersV a 2 = 3 * a / 2 := by
  have h := beukersV_step a 0
  norm_num at h
  rw [beukersV_one, beukersV_zero] at h
  field_simp at h ⊢
  nlinarith

lemma beukersV_three (a : ℚ) : beukersV a 3 = (15 * a ^ 2 - 4) / 6 := by
  have h := beukersV_step a 1
  norm_num at h
  rw [beukersV_one, beukersV_two] at h
  field_simp at h ⊢
  nlinarith

lemma beukersH_coeff_zero (a : ℚ) : PowerSeries.coeff 0 (beukersH a) = 0 := by
  rw [beukersH_coeff, beukersV_zero]

lemma beukersH_coeff_one (a : ℚ) : PowerSeries.coeff 1 (beukersH a) = 1 := by
  rw [beukersH_coeff, beukersV_one]

lemma beukersH_coeff_two (a : ℚ) : PowerSeries.coeff 2 (beukersH a) = 3 * a / 2 := by
  rw [beukersH_coeff, beukersV_two]

/-- the homogeneous recurrence of `v` at index `n ≥ 1` (same as `u`) -/
lemma beukersV_homogeneous (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℚ) + 1) * beukersV a (n + 1) =
      ((2 * (n : ℚ)) + 1) * a * beukersV a n - (n : ℚ) * beukersV a (n - 1) := by
  have h := beukersV_step a (n - 1)
  have hidx1 : (n - 1) + 2 = n + 1 := by omega
  have hidx2 : (n - 1) + 1 = n := by omega
  rw [hidx1, hidx2] at h
  have hc1 : (((n - 1 : ℕ) : ℚ) + 2) = ((n : ℚ) + 1) := by
    calc
      (((n - 1 : ℕ) : ℚ) + 2) = ((n - 1 + 2 : ℕ) : ℚ) := by norm_num
      _ = ((n + 1 : ℕ) : ℚ) := by rw [hidx1]
      _ = ((n : ℚ) + 1) := by norm_num
  have hc2 : ((2 * ((n - 1 : ℕ) : ℚ)) + 3) = ((2 * (n : ℚ)) + 1) := by
    have hN : 2 * (n - 1) + 3 = 2 * n + 1 := by omega
    calc
      ((2 * ((n - 1 : ℕ) : ℚ)) + 3) = (((2 * (n - 1) + 3 : ℕ)) : ℚ) := by norm_num
      _ = (((2 * n + 1 : ℕ)) : ℚ) := by rw [hN]
      _ = ((2 * (n : ℚ)) + 1) := by norm_num
  have hc3 : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
    calc
      (((n - 1 : ℕ) : ℚ) + 1) = ((n - 1 + 1 : ℕ) : ℚ) := by norm_num
      _ = (n : ℚ) := congrArg (fun x : ℕ => (x : ℚ)) (by omega : n - 1 + 1 = n)
  rw [hc1, hc2, hc3] at h
  exact h

/-- coefficient form of the inhomogeneous ODE (RHS = 1):
`(1 − 2a·X + X²)·H′ + (X − a)·H = 1`. -/
lemma beukersH_ode_coeff (a : ℚ) (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) *
        (PowerSeries.derivative (R := ℚ) (beukersH a)) + (X - C a) * beukersH a) =
      (if n = 0 then 1 else 0) := by
  classical
  let V : ℕ → ℚ := beukersV a
  have hV : ∀ m, PowerSeries.coeff m (beukersH a) = V m := by
    intro m
    exact beukersH_coeff a m
  have hV0 : V 0 = 0 := beukersV_zero a
  have hV1 : V 1 = 1 := beukersV_one a
  have hstep : ∀ m : ℕ, 1 ≤ m →
      ((m : ℚ) + 1) * V (m + 1) =
        ((2 * (m : ℚ)) + 1) * a * V m - (m : ℚ) * V (m - 1) := by
    intro m hm
    exact beukersV_homogeneous a hm
  have hderiv : ∀ m, PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) (beukersH a)) = V (m + 1) * ((m : ℚ) + 1) := by
    intro m
    rw [PowerSeries.coeff_derivative, hV]
  have hsplit :
      ((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) * (PowerSeries.derivative (R := ℚ) (beukersH a))
        + (X - C a) * beukersH a
      = (PowerSeries.derivative (R := ℚ) (beukersH a)) - C (2 * a) * (X * PowerSeries.derivative (R := ℚ) (beukersH a))
        + X ^ 2 * (PowerSeries.derivative (R := ℚ) (beukersH a)) + X * beukersH a - C a * beukersH a := by
    ring
  rw [hsplit]
  simp only [map_add, map_sub, map_neg]
  let F : PowerSeries ℚ := beukersH a
  let dF : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (beukersH a)
  have hC2 : ∀ m : ℕ, PowerSeries.coeff m (C (2 * a) * (X * dF)) = (2 * a) * PowerSeries.coeff m (X * dF) := by
    intro m
    exact PowerSeries.coeff_C_mul m (X * dF) (2 * a)
  have hCa : ∀ m : ℕ, PowerSeries.coeff m (C a * F) = a * PowerSeries.coeff m F := by
    intro m
    exact PowerSeries.coeff_C_mul m F a
  have hXm : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 1) (X * g) = PowerSeries.coeff m g := by
    intro g m
    simpa using (PowerSeries.coeff_X_pow_mul g 1 m)
  have hX2m : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 2) (X ^ 2 * g) = PowerSeries.coeff m g := by
    intro g m
    exact PowerSeries.coeff_X_pow_mul g 2 m
  have hcoeff_dF : ∀ m : ℕ, PowerSeries.coeff m dF = V (m + 1) * (↑m + 1) := by
    intro m
    rw [show dF = PowerSeries.derivative (R := ℚ) (beukersH a) from rfl, hderiv m]
  have hcoeff_F : ∀ m : ℕ, PowerSeries.coeff m F = V m := by
    intro m
    rw [show F = beukersH a from rfl, hV m]
  cases n with
  | zero =>
      have hz1 : PowerSeries.coeff 0 (X * dF) = 0 := by simp
      have hz2 : PowerSeries.coeff 0 (X ^ 2 * dF) = 0 := by simp
      have hz3 : PowerSeries.coeff 0 (X * F) = 0 := by simp
      rw [hC2 0, hCa 0, hz1, hz2, hz3, hcoeff_dF 0, hcoeff_F 0]
      simp [hV0, hV1]
  | succ m =>
      cases m with
      | zero =>
          -- n = 1: RHS = 0
          have hx1 : PowerSeries.coeff 1 (X * dF) = PowerSeries.coeff 0 dF := by
            simpa using (hXm dF 0)
          have hx2 : PowerSeries.coeff 1 (X ^ 2 * dF) = 0 := by
            simpa [pow_two, mul_assoc] using (hXm (X * dF) 0)
          have hx3 : PowerSeries.coeff 1 (X * F) = PowerSeries.coeff 0 F := by
            simpa using (hXm F 0)
          rw [hC2 1, hCa 1, hx1, hx2, hx3, hcoeff_dF 1, hcoeff_F 1]
          rw [hcoeff_dF 0, hcoeff_F 0]
          have h1 := hstep 1 (by norm_num)
          norm_num at h1 ⊢
          nlinarith [h1, hV0, hV1]
      | succ k =>
          have hx1 : PowerSeries.coeff (k + 2) (X * dF) = PowerSeries.coeff (k + 1) dF := by
            simpa [Nat.add_assoc] using (hXm dF (k + 1))
          have hx2 : PowerSeries.coeff (k + 2) (X ^ 2 * dF) = PowerSeries.coeff k dF := by
            exact hX2m dF k
          have hx3 : PowerSeries.coeff (k + 2) (X * F) = PowerSeries.coeff (k + 1) F := by
            simpa [Nat.add_assoc] using (hXm F (k + 1))
          rw [hC2 (k + 2), hCa (k + 2), hx1, hx2, hx3, hcoeff_dF (k + 2), hcoeff_F (k + 2)]
          rw [hcoeff_dF (k + 1), hcoeff_dF k, hcoeff_F (k + 1)]
          rw [show (k + 2) + 1 = k + 3 by omega, show (k + 1) + 1 = k + 2 by omega]
          have hs2 := hstep (k + 2) (by omega)
          rw [show (k + 2) + 1 = k + 3 by omega, show k + 2 - 1 = k + 1 by omega] at hs2
          ring_nf at hs2 ⊢
          simp only [Nat.cast_add, Nat.cast_one] at hs2 ⊢
          simp [show k + 2 ≠ 0 by omega]
          linear_combination hs2

/-- the inhomogeneous ODE of the Apéry companion:
`(1 − 2a·X + X²)·H′ + (X − a)·H = 1`. -/
lemma beukersH_ode (a : ℚ) :
    ((1 : PowerSeries ℚ) - C (2 * a) * X + X ^ 2) * (PowerSeries.derivative (R := ℚ) (beukersH a))
      + (X - C a) * beukersH a = (1 : PowerSeries ℚ) := by
  apply PowerSeries.ext
  intro n
  rw [beukersH_ode_coeff a n]
  simp

/-! ## Connecting the two recurrences: shared homogeneous step and Casoratian

Both `u` and `v` satisfy the *same* homogeneous second-order recurrence for
every index (`beukersU_step`, `beukersV_step`; index-shifted forms
`beukersU_homogeneous`, `beukersV_homogeneous` for `n ≥ 1`).  Hence the
*Casoratian* `n·(uₙ·vₙ₋₁ − uₙ₋₁·vₙ)` is invariant under `n ↦ n+1`
(`beukersUV_casoratian_step`) and is constant for all `n ≥ 1`
(`beukersUV_casoratian_const`); its value, computed at `n = 1`, is `−1`
(`beukersUV_casoratian_value`).  This yields the *ratio-difference*
identity `beukersUV_ratio_diff`:
`vₙ/uₙ − vₙ₋₁/uₙ₋₁ = 1/(n·uₙ·uₙ₋₁)`,
whose telescoping (`beukersUV_telescope`) is the algebraic seed of the
Apéry limit `lim vₙ/uₙ = ½·log((a+1)/(a−1))`.
-/

/-- the homogeneous recurrence of `u` at index `n ≥ 1` -/
lemma beukersU_homogeneous (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℚ) + 1) * beukersU a (n + 1) =
      ((2 * (n : ℚ)) + 1) * a * beukersU a n - (n : ℚ) * beukersU a (n - 1) := by
  have h := beukersU_step a (n - 1)
  have hidx1 : (n - 1) + 2 = n + 1 := by omega
  have hidx2 : (n - 1) + 1 = n := by omega
  rw [hidx1, hidx2] at h
  have hc1 : (((n - 1 : ℕ) : ℚ) + 2) = ((n : ℚ) + 1) := by
    calc
      (((n - 1 : ℕ) : ℚ) + 2) = ((n - 1 + 2 : ℕ) : ℚ) := by norm_num
      _ = ((n + 1 : ℕ) : ℚ) := by rw [hidx1]
      _ = ((n : ℚ) + 1) := by norm_num
  have hc2 : ((2 * ((n - 1 : ℕ) : ℚ)) + 3) = ((2 * (n : ℚ)) + 1) := by
    have hN : 2 * (n - 1) + 3 = 2 * n + 1 := by omega
    calc
      ((2 * ((n - 1 : ℕ) : ℚ)) + 3) = (((2 * (n - 1) + 3 : ℕ)) : ℚ) := by norm_num
      _ = (((2 * n + 1 : ℕ)) : ℚ) := by rw [hN]
      _ = ((2 * (n : ℚ)) + 1) := by norm_num
  have hc3 : (((n - 1 : ℕ) : ℚ) + 1) = (n : ℚ) := by
    calc
      (((n - 1 : ℕ) : ℚ) + 1) = ((n - 1 + 1 : ℕ) : ℚ) := by norm_num
      _ = (n : ℚ) := congrArg (fun x : ℕ => (x : ℚ)) (by omega : n - 1 + 1 = n)
  rw [hc1, hc2, hc3] at h
  exact h

/-- the Casoratian invariance step: for `n ≥ 1`, `Wₙ₊₁ = Wₙ` -/
lemma beukersUV_casoratian_step (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℚ) + 1) * (beukersU a (n + 1) * beukersV a n - beukersU a n * beukersV a (n + 1)) =
      (n : ℚ) * (beukersU a n * beukersV a (n - 1) - beukersU a (n - 1) * beukersV a n) := by
  have hu := beukersU_homogeneous a hn
  have hv := beukersV_homogeneous a hn
  calc
    ((n : ℚ) + 1) * (beukersU a (n + 1) * beukersV a n - beukersU a n * beukersV a (n + 1))
        = ((n : ℚ) + 1) * beukersU a (n + 1) * beukersV a n -
            beukersU a n * (((n : ℚ) + 1) * beukersV a (n + 1)) := by ring
    _ = (((2 * (n : ℚ)) + 1) * a * beukersU a n - (n : ℚ) * beukersU a (n - 1)) * beukersV a n -
          beukersU a n * (((2 * (n : ℚ)) + 1) * a * beukersV a n - (n : ℚ) * beukersV a (n - 1)) := by
          rw [hu, hv]
    _ = (n : ℚ) * (beukersU a n * beukersV a (n - 1) - beukersU a (n - 1) * beukersV a n) := by ring

/-- the Casoratian is constant from index 1 on -/
lemma beukersUV_casoratian_const (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℚ) * (beukersU a n * beukersV a (n - 1) - beukersU a (n - 1) * beukersV a n) =
      (1 : ℚ) * (beukersU a 1 * beukersV a 0 - beukersU a 0 * beukersV a 1) := by
  let P : ℕ → Prop := fun m =>
    (m : ℚ) * (beukersU a m * beukersV a (m - 1) - beukersU a (m - 1) * beukersV a m) =
      (1 : ℚ) * (beukersU a 1 * beukersV a 0 - beukersU a 0 * beukersV a 1)
  have hbase : P 1 := by
    dsimp [P]
  have hstep : ∀ m ≥ 1, P m → P (m + 1) := by
    intro m hm ih
    dsimp [P] at ih ⊢
    have hst := beukersUV_casoratian_step a hm
    simp only [Nat.cast_add, Nat.cast_one] at hst ⊢
    rw [hst]
    exact ih
  exact Nat.le_induction hbase hstep n hn

/-- evaluation of the Casoratian: `n·(uₙvₙ₋₁ − uₙ₋₁vₙ) = −1` for `n ≥ 1` -/
lemma beukersUV_casoratian_value (a : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℚ) * (beukersU a n * beukersV a (n - 1) - beukersU a (n - 1) * beukersV a n) = -1 := by
  have hc := beukersUV_casoratian_const a hn
  have hW1 : (1 : ℚ) * (beukersU a 1 * beukersV a 0 - beukersU a 0 * beukersV a 1) = -1 := by
    rw [beukersU_one, beukersV_zero, beukersU_zero, beukersV_one]
    ring_nf
  rw [hc, hW1]

/-- ratio difference of the two coefficient families (seed of the Apéry
limit): for `n ≥ 2` with `uₙ, uₙ₋₁ ≠ 0`,
`vₙ/uₙ − vₙ₋₁/uₙ₋₁ = 1/(n·uₙ·uₙ₋₁)`. -/
lemma beukersUV_ratio_diff (a : ℚ) {n : ℕ} (hn : 2 ≤ n)
    (hu : beukersU a n ≠ 0) (hu1 : beukersU a (n - 1) ≠ 0) :
    beukersV a n / beukersU a n - beukersV a (n - 1) / beukersU a (n - 1) =
      (1 : ℚ) / ((n : ℚ) * beukersU a n * beukersU a (n - 1)) := by
  have hW := beukersUV_casoratian_value a (by omega : 1 ≤ n)
  field_simp [hu, hu1]
  have hW' : (beukersU a (n - 1) * beukersV a n - beukersU a n * beukersV a (n - 1)) * (n : ℚ) = 1 := by
    nlinarith [hW]
  nlinarith

/-- finite telescoping of the ratio differences (the algebraic spine of the
Apéry limit): for `N ≥ 4` with `u₃,…,uₙ ≠ 0`,
`v_N/u_N − v₃/u₃ = Σ_{k=4}^{N} 1/(k·uₖ·uₖ₋₁)`. -/
lemma beukersUV_telescope (a : ℚ) {N : ℕ} (hN : 4 ≤ N)
    (hu : ∀ j, 3 ≤ j → j ≤ N → beukersU a j ≠ 0) :
    beukersV a N / beukersU a N - beukersV a 3 / beukersU a 3 =
      ∑ k ∈ Finset.Icc 4 N, (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) := by
  classical
  let r : ℕ → ℚ := fun m => beukersV a m / beukersU a m
  have hr : ∀ k ∈ Finset.Icc 4 N,
      r k - r (k - 1) = (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) := by
    intro k hk
    have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    dsimp [r]
    apply beukersUV_ratio_diff a (by omega : 2 ≤ k)
    · exact hu k (by omega) hkN
    · exact hu (k - 1) (by omega) (by omega)
  have htel : (∑ k ∈ Finset.Icc 4 N, (r k - r (k - 1))) = r N - r 3 := by
    have hmain : ∀ n ≥ 4, (∑ k ∈ Finset.Icc 4 n, (r k - r (k - 1))) = r n - r 3 := by
      refine Nat.le_induction ?base ?step
      · simp
      · intro n hn ih
        rw [Finset.sum_Icc_succ_top (by omega : 4 ≤ n + 1)]
        rw [ih]
        rw [show (n + 1) - 1 = n by omega]
        ring
    exact hmain N hN
  calc
    beukersV a N / beukersU a N - beukersV a 3 / beukersU a 3 = r N - r 3 := rfl
    _ = (∑ k ∈ Finset.Icc 4 N, (r k - r (k - 1))) := htel.symm
    _ = ∑ k ∈ Finset.Icc 4 N, (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hr k hk



/-! ## Growth of `u_n` (lower bounds from the recurrence)

For real `a ≥ 1` the coefficients `u_n(a)` of `A(a,x)` are positive,
grow at least geometrically with ratio `a` (`beukersU_ratio`), and hence
satisfy the lower bound `uₙ ≥ aⁿ` (`beukersU_lower_bound`).  This is the
input that makes the tail of the ratio-difference series converge (the
summand `1/(k·uₖ·uₖ₋₁)` is bounded by the geometric `1/(k·a^{2k−1})`,
`beukersU_recip_le`), which is the analytic half of the Apéry limit.
(For the CDT application `a = 1+2m`, `m ≥ 1`, so `a ≥ 3`; the cases with
negative `m` reduce to these by the parity `uₙ(−a) = (−1)ⁿuₙ(a)`.)
-/

/-- geometric growth of the ratios: for `a ≥ 1`, `u_{n+1} ≥ a·uₙ` -/
lemma beukersU_ratio (a : ℚ) (ha : 1 ≤ a) : ∀ n : ℕ, beukersU a (n + 1) ≥ a * beukersU a n := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hasq : 1 ≤ a * a := by nlinarith
  have hmain : ∀ n, beukersU a (n + 1) ≥ a * beukersU a n ∧ 0 ≤ beukersU a n := by
    intro n
    induction n with
    | zero =>
        constructor <;> simp [beukersU]
    | succ m ih =>
        constructor
        · rcases ih with ⟨hge, hnn⟩
          have hrec := beukersU_step a m
          have hdiff : ((m : ℚ) + 2) * (beukersU a (m + 2) - a * beukersU a (m + 1))
              = ((m : ℚ) + 1) * (a * beukersU a (m + 1) - beukersU a m) := by
            nlinarith [hrec]
          have haum1 : a * beukersU a (m + 1) ≥ a * (a * beukersU a m) :=
            mul_le_mul_of_nonneg_left hge ha0
          have haum2 : a * (a * beukersU a m) ≥ beukersU a m := by
            have hc : 0 ≤ (a * a - 1) * beukersU a m := mul_nonneg (sub_nonneg.mpr hasq) hnn
            nlinarith
          have hRHS : 0 ≤ a * beukersU a (m + 1) - beukersU a m := by
            nlinarith
          have hm2 : 0 < (m : ℚ) + 2 := by positivity
          have hm1 : 0 ≤ (m : ℚ) + 1 := by positivity
          have hnonneg : 0 ≤ beukersU a (m + 2) - a * beukersU a (m + 1) := by
            have hmul : 0 ≤ ((m : ℚ) + 2) * (beukersU a (m + 2) - a * beukersU a (m + 1)) := by
              rw [hdiff]
              exact mul_nonneg hm1 hRHS
            rw [mul_comm] at hmul
            exact nonneg_of_mul_nonneg_left hmul hm2
          linarith
        · rcases ih with ⟨hge, hnn⟩
          exact le_trans (mul_nonneg ha0 hnn) hge
  exact fun n => (hmain n).1

/-- positivity of the coefficients for `a ≥ 1` -/
lemma beukersU_pos (a : ℚ) (ha : 1 ≤ a) (n : ℕ) : 0 < beukersU a n := by
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  induction n with
  | zero => simp [beukersU]
  | succ m ih =>
      exact lt_of_lt_of_le (mul_pos hapos ih) (beukersU_ratio a ha m)

/-- lower bound `uₙ ≥ aⁿ` for `a ≥ 1` -/
lemma beukersU_lower_bound (a : ℚ) (ha : 1 ≤ a) : ∀ n : ℕ, a ^ n ≤ beukersU a n := by
  intro n
  induction n with
  | zero => simp [beukersU]
  | succ m ih =>
      have h1 := beukersU_ratio a ha m
      have h2 : a * beukersU a m ≥ a * a ^ m :=
        mul_le_mul_of_nonneg_left ih (le_trans zero_le_one ha)
      have h3 : a * a ^ m = a ^ (m + 1) := by
        rw [pow_succ, mul_comm]
      nlinarith

/-- the tail-summand bound: `1/(k·uₖ·uₖ₋₁) ≤ 1/(k·a^(2k−1))` for `a ≥ 1`,
`k ≥ 1` — geometric decay for `a > 1`, giving convergence of the Apéry
tail `Σ_k 1/(k·uₖ·uₖ₋₁)`. -/
lemma beukersU_recip_le (a : ℚ) (ha : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) ≤
      (1 : ℚ) / ((k : ℚ) * a ^ (k + (k - 1))) := by
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hkpos : 0 < (k : ℚ) := by exact_mod_cast hk
  have huk : 0 < beukersU a k := beukersU_pos a ha k
  have huk1 : 0 < beukersU a (k - 1) := beukersU_pos a ha (k - 1)
  have hpk : 0 < a ^ (k + (k - 1)) := pow_pos hapos (k + (k - 1))
  have hD1pos : 0 < (k : ℚ) * beukersU a k * beukersU a (k - 1) := mul_pos (mul_pos hkpos huk) huk1
  have hD2pos : 0 < (k : ℚ) * a ^ (k + (k - 1)) := mul_pos hkpos hpk
  have hden : (k : ℚ) * a ^ (k + (k - 1)) ≤ (k : ℚ) * beukersU a k * beukersU a (k - 1) := by
    have hb1 : a ^ k ≤ beukersU a k := beukersU_lower_bound a ha k
    have hb2 : a ^ (k - 1) ≤ beukersU a (k - 1) := beukersU_lower_bound a ha (k - 1)
    have hpr : a ^ k * a ^ (k - 1) ≤ beukersU a k * beukersU a (k - 1) :=
      mul_le_mul hb1 hb2 (le_of_lt (pow_pos hapos (k - 1))) (le_of_lt huk)
    have hpw : a ^ (k + (k - 1)) = a ^ k * a ^ (k - 1) := by rw [pow_add]
    rw [hpw]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hpr (le_of_lt hkpos)
  -- 1/(k·u) ≤ 1/(k·a^{..}) from (k·a^{..}) ≤ (k·u) with positivity
  field_simp [ne_of_gt hD1pos, ne_of_gt hD2pos]
  nlinarith



/-! ## Parity: reducing negative parameters to positive ones

For the CDT application one needs `u_n(a), v_n(a)` at `a = 1 + 2m` with
`m ≤ -2` (i.e. `a ≤ -3`).  The parity identities
`u_n(-a) = (-1)^n·u_n(a)`, `v_n(-a) = (-1)^{n+1}·v_n(a)` reduce every
negative-`a` statement (growth, summability, integrality) to the positive
case `|a| ≥ 3` handled below.  Both recurrences have the same homogeneous
shape for `n ≥ 0`, so the sign bookkeeping is uniform.
-/

/-- `(-1)^(n+2) = (-1)^n` in `ℚ` -/
lemma neg_one_pow_add_two_q (n : ℕ) : (-1 : ℚ) ^ (n + 2) = (-1 : ℚ) ^ n := by
  rw [pow_add]
  norm_num

/-- `(-1)^(n+1) = -(-1)^n` in `ℚ` -/
lemma neg_one_pow_succ_neg_q (n : ℕ) : (-1 : ℚ) ^ (n + 1) = -((-1 : ℚ) ^ n) := by
  rw [pow_succ]
  ring

/-- parity of the `u` coefficients: `u_n(-a) = (-1)^n·u_n(a)` -/
lemma beukersU_neg_mul (a : ℚ) : ∀ n : ℕ, beukersU (-a) n = (-1 : ℚ) ^ n * beukersU a n := by
  intro n
  have hmain : ∀ m, beukersU (-a) m = (-1 : ℚ) ^ m * beukersU a m ∧
                   beukersU (-a) (m + 1) = (-1 : ℚ) ^ (m + 1) * beukersU a (m + 1) := by
    intro m
    induction m with
    | zero =>
        constructor <;> simp [beukersU]
    | succ m ih =>
        rcases ih with ⟨h0, h1⟩
        constructor
        · exact h1
        · have hstepA := beukersU_step a m
          have hstepB := beukersU_step (-a) m
          have hcanc : (m : ℚ) + 2 ≠ 0 := by positivity
          have hs2 : (-1 : ℚ) ^ (m + 1) = -((-1 : ℚ) ^ m) := neg_one_pow_succ_neg_q m
          have hs1 : (-1 : ℚ) ^ (m + 2) = (-1 : ℚ) ^ m := neg_one_pow_add_two_q m
          apply mul_left_cancel₀ hcanc
          calc
            ((m : ℚ) + 2) * beukersU (-a) (m + 2)
                = ((2 * (m : ℚ)) + 3) * (-a) * beukersU (-a) (m + 1)
                    - ((m : ℚ) + 1) * beukersU (-a) m := hstepB
            _ = ((2 * (m : ℚ)) + 3) * (-a) * ((-1 : ℚ) ^ (m + 1) * beukersU a (m + 1))
                    - ((m : ℚ) + 1) * ((-1 : ℚ) ^ m * beukersU a m) := by rw [h1, h0]
            _ = ((2 * (m : ℚ)) + 3) * a * ((-1 : ℚ) ^ (m + 2)) * beukersU a (m + 1)
                    - ((m : ℚ) + 1) * ((-1 : ℚ) ^ (m + 2)) * beukersU a m := by
                        rw [hs2, hs1]
                        ring
            _ = ((-1 : ℚ) ^ (m + 2)) * (((2 * (m : ℚ)) + 3) * a * beukersU a (m + 1)
                    - ((m : ℚ) + 1) * beukersU a m) := by ring
            _ = ((-1 : ℚ) ^ (m + 2)) * (((m : ℚ) + 2) * beukersU a (m + 2)) := by rw [hstepA]
            _ = ((m : ℚ) + 2) * ((-1 : ℚ) ^ (m + 2) * beukersU a (m + 2)) := by ring
  exact (hmain n).1

/-- parity of the `v` coefficients: `v_n(-a) = (-1)^(n+1)·v_n(a)` -/
lemma beukersV_neg_mul (a : ℚ) : ∀ n : ℕ, beukersV (-a) n = (-1 : ℚ) ^ (n + 1) * beukersV a n := by
  intro n
  have hmain : ∀ m, beukersV (-a) m = (-1 : ℚ) ^ (m + 1) * beukersV a m ∧
                   beukersV (-a) (m + 1) = (-1 : ℚ) ^ ((m + 1) + 1) * beukersV a (m + 1) := by
    intro m
    induction m with
    | zero =>
        constructor
        · simp [beukersV]
        · simp [beukersV]
    | succ m ih =>
        rcases ih with ⟨h0, h1⟩
        constructor
        · exact h1
        · have hstepA := beukersV_step a m
          have hstepB := beukersV_step (-a) m
          have hcanc : (m : ℚ) + 2 ≠ 0 := by positivity
          have hs3 : (-1 : ℚ) ^ (m + 3) = (-1 : ℚ) ^ (m + 1) := by
            rw [show (m + 3) = (m + 1) + 2 by omega]
            exact neg_one_pow_add_two_q (m + 1)
          have hs2 : (-1 : ℚ) ^ (m + 2) = -((-1 : ℚ) ^ (m + 1)) := neg_one_pow_succ_neg_q (m + 1)
          apply mul_left_cancel₀ hcanc
          calc
            ((m : ℚ) + 2) * beukersV (-a) (m + 2)
                = ((2 * (m : ℚ)) + 3) * (-a) * beukersV (-a) (m + 1)
                    - ((m : ℚ) + 1) * beukersV (-a) m := hstepB
            _ = ((2 * (m : ℚ)) + 3) * (-a) * ((-1 : ℚ) ^ ((m + 1) + 1) * beukersV a (m + 1))
                    - ((m : ℚ) + 1) * ((-1 : ℚ) ^ (m + 1) * beukersV a m) := by rw [h1, h0]
            _ = ((2 * (m : ℚ)) + 3) * a * ((-1 : ℚ) ^ (m + 3)) * beukersV a (m + 1)
                    - ((m : ℚ) + 1) * ((-1 : ℚ) ^ (m + 3)) * beukersV a m := by
                        rw [hs2, hs3]
                        ring
            _ = ((-1 : ℚ) ^ (m + 3)) * (((2 * (m : ℚ)) + 3) * a * beukersV a (m + 1)
                    - ((m : ℚ) + 1) * beukersV a m) := by ring
            _ = ((-1 : ℚ) ^ (m + 3)) * (((m : ℚ) + 2) * beukersV a (m + 2)) := by rw [hstepA]
            _ = ((m : ℚ) + 2) * ((-1 : ℚ) ^ ((m + 2) + 1) * beukersV a (m + 2)) := by
                rw [show (m + 3) = (m + 2) + 1 by omega]
                ring
  exact (hmain n).1


/-! ## Real convergence of the Apéry tail series

The analytic half of the Apéry-limit machinery of §"Products of two
logarithms" of the CDT paper: for `a ≥ 1` all `u_k(a)` are positive and
grow at least geometrically with ratio `a` (proved above), so the tail
series

`Σ_{k ≥ 4} 1/(k·uₖ·uₖ₋₁)`

converges (absolutely, as a positive series) for `a > 1` — indeed for
`a ≥ 3` (the CDT range, `a = 1+2m`, `m ≥ 1`) the terms are bounded by the
geometric `(a:ℝ)^{-k}`.  Combined with the finite telescoping identity
`beukersUV_telescope_pos` (cast to `ℝ`), this shows the Apéry ratio
sequence `v_N(a)/u_N(a)` converges in `ℝ`

`lim_{N→∞} v_N/u_N = v₃/u₃ + Σ_{k≥4} 1/(k·uₖ·uₖ₋₁)`   (`beukersUV_apéry_tendsto`)

— the existence side of the Apéry limit; the identification of the limit
with `½·log((a+1)/(a−1))` (paper eq. (beukerslimit)) is the next (analytic)
brick.  Notation: `beukersRTerm a k` is the ℝ-valued summand and
`beukersTail4 a j = beukersRTerm a (j+4)` re-indexes the tail from `k = 4`.
-/

/-- real-valued summand of the Apéry tail: `1/(k·uₖ(a)·uₖ₋₁(a))` -/
def beukersRTerm (a : ℚ) (k : ℕ) : ℝ :=
  (1 : ℝ) / ((k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ))

/-- the ℝ summand is the cast of the ℚ one -/
lemma beukersRTerm_eq_cast (a : ℚ) (k : ℕ) :
    beukersRTerm a k = (((1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) : ℚ) : ℝ) := by
  dsimp [beukersRTerm]
  norm_num

/-- shifted tail term: `beukersTail4 a j = beukersRTerm a (j + 4)` -/
def beukersTail4 (a : ℚ) (j : ℕ) : ℝ := beukersRTerm a (j + 4)

/-- the finite telescoping identity without hypotheses on the `u`'s
(positivity of the `u`'s from `beukersU_pos` covers the nonvanishing). -/
lemma beukersUV_telescope_pos (a : ℚ) (ha : 1 ≤ a) {N : ℕ} (hN : 4 ≤ N) :
    beukersV a N / beukersU a N - beukersV a 3 / beukersU a 3 =
      ∑ k ∈ Finset.Icc 4 N, (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1)) := by
  exact beukersUV_telescope a hN (fun j _ _ => ne_of_gt (beukersU_pos a ha j))

/-- reindexing `k ∈ Icc 4 N` as `j = k - 4 ∈ range (N - 3)` -/
lemma sum_Icc4_eq_range (f : ℕ → ℚ) : ∀ {N : ℕ}, 4 ≤ N →
    (∑ k ∈ Finset.Icc 4 N, f k) = ∑ j ∈ Finset.range (N - 3), f (j + 4) := by
  intro N hN
  symm
  refine Finset.sum_bij (fun j _ => j + 4) ?_ ?_ ?_ ?_
  · intro j hj
    have hjlt : j < N - 3 := Finset.mem_range.mp hj
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro a _ b _ hab
    omega
  · intro k hk
    have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    refine ⟨k - 4, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    rfl

/-- the real-valued telescoping identity: `r_N = r_3 + (partial sums of the tail)` -/
lemma beukersUV_real_telescope (a : ℚ) (ha : 1 ≤ a) {N : ℕ} (hN : 4 ≤ N) :
    (beukersV a N / beukersU a N : ℝ) =
      (beukersV a 3 / beukersU a 3 : ℝ) + ∑ j ∈ Finset.range (N - 3), beukersTail4 a j := by
  have htel := beukersUV_telescope_pos a ha hN
  have htel' : (beukersV a N / beukersU a N - beukersV a 3 / beukersU a 3 : ℚ) =
      ∑ j ∈ Finset.range (N - 3), (1 : ℚ) / (((j + 4 : ℕ) : ℚ) * beukersU a (j + 4) * beukersU a ((j + 4) - 1)) := by
    rw [htel]
    exact sum_Icc4_eq_range (fun k => (1 : ℚ) / ((k : ℚ) * beukersU a k * beukersU a (k - 1))) hN
  have hcast : ((beukersV a N / beukersU a N - beukersV a 3 / beukersU a 3 : ℚ) : ℝ) =
      ∑ j ∈ Finset.range (N - 3), beukersTail4 a j := by
    rw [htel']
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [beukersTail4]
    exact (beukersRTerm_eq_cast a (j + 4)).symm
  have hL : (beukersV a N / beukersU a N : ℝ) - (beukersV a 3 / beukersU a 3 : ℝ)
      = ∑ j ∈ Finset.range (N - 3), beukersTail4 a j := by
    simpa using hcast
  nlinarith

/-- cast of the ℚ tail bound to ℝ: `1/(k·uₖ·uₖ₋₁) ≤ 1/(k·a^(k+(k−1)))` -/
lemma beukersU_recip_le_real (a : ℚ) (ha : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / ((k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ)) ≤
      (1 : ℝ) / ((k : ℝ) * (a : ℝ) ^ (k + (k - 1))) := by
  have hq := beukersU_recip_le a ha hk
  exact_mod_cast hq

/-- geometric bound: `1/(k·a^(k+(k−1))) ≤ a^{-k}` for `a ≥ 1`, `k ≥ 1` -/
lemma beukers_geom_bound (a : ℚ) (ha1 : 1 ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / ((k : ℝ) * (a : ℝ) ^ (k + (k - 1))) ≤ ((a : ℝ) ^ k)⁻¹ := by
  have hapos : 0 < (a : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) ha1)
  have hpowpos : 0 < (a : ℝ) ^ k := pow_pos hapos k
  have hle : (a : ℝ) ^ k ≤ (k : ℝ) * (a : ℝ) ^ (k + (k - 1)) := by
    have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have hake : 1 ≤ (a : ℝ) := by exact_mod_cast ha1
    have hx1 : 1 ≤ (a : ℝ) ^ (k - 1) := one_le_pow₀ hake
    have hprod : 1 ≤ (k : ℝ) * (a : ℝ) ^ (k - 1) := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hprod (pow_nonneg (le_of_lt hapos) k)
    calc
      (a : ℝ) ^ k = 1 * (a : ℝ) ^ k := by ring
      _ ≤ ((k : ℝ) * (a : ℝ) ^ (k - 1)) * (a : ℝ) ^ k := by exact hmul
      _ = (k : ℝ) * ((a : ℝ) ^ (k - 1) * (a : ℝ) ^ k) := by ring
      _ = (k : ℝ) * (a : ℝ) ^ ((k - 1) + k) := by rw [← pow_add]
      _ = (k : ℝ) * (a : ℝ) ^ (k + (k - 1)) := by rw [add_comm]
  simpa using (one_div_le_one_div_of_le hpowpos hle)

/-- termwise: `t_k ≤ a^{-k}` for all `k` (the case `k = 0` is trivial) -/
lemma beukers_term_le (a : ℚ) (ha1 : 1 ≤ a) (k : ℕ) :
    (1 : ℝ) / ((k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ)) ≤ ((a : ℝ) ^ k)⁻¹ := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hk : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    exact le_trans (beukersU_recip_le_real a ha1 hk) (beukers_geom_bound a ha1 hk)

/-- nonnegativity of the real terms -/
lemma beukers_term_nonneg (a : ℚ) (ha1 : 1 ≤ a) (k : ℕ) :
    0 ≤ (1 : ℝ) / ((k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ)) := by
  by_cases hk0 : k = 0
  · subst k; simp
  · have hk : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have huk : 0 < (beukersU a k : ℝ) := by
      exact_mod_cast beukersU_pos a ha1 k
    have huk1 : 0 < (beukersU a (k - 1) : ℝ) := by
      exact_mod_cast beukersU_pos a ha1 (k - 1)
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hden : 0 < (k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ) :=
      mul_pos (mul_pos hkpos huk) huk1
    exact le_of_lt (one_div_pos.mpr hden)

/-- summability over `ℕ` of the Apéry tail summands for `a ≥ 3`
(geometric domination `t_k ≤ a^{-k}`, `Σ_k a^{-k} = 1/(a−1) < ∞`) -/
theorem beukersUV_series_summable (a : ℚ) (ha3 : 3 ≤ a) :
    Summable (fun k : ℕ =>
      (1 : ℝ) / ((k : ℝ) * (beukersU a k : ℝ) * (beukersU a (k - 1) : ℝ))) := by
  classical
  have ha1 : 1 ≤ a := le_trans (by norm_num) ha3
  have hapos_q : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) ha1
  have hapos : 0 < (a : ℝ) := by exact_mod_cast hapos_q
  have hainv : (a : ℝ)⁻¹ < 1 := by
    have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha3
    have hinv : (a : ℝ)⁻¹ ≤ (1 / 3 : ℝ) := by
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) h3)
    exact lt_of_le_of_lt hinv (by norm_num)
  have hsum : Summable (fun k : ℕ => ((a : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (le_of_lt hapos)) hainv
  have hrew : (fun k : ℕ => ((a : ℝ) ^ k)⁻¹) = (fun k : ℕ => ((a : ℝ)⁻¹) ^ k) := by
    funext k
    exact (inv_pow (a : ℝ) k).symm
  have hsum2 : Summable (fun k : ℕ => ((a : ℝ) ^ k)⁻¹) := by
    rwa [hrew]
  exact Summable.of_nonneg_of_le (beukers_term_nonneg a ha1) (beukers_term_le a ha1) hsum2

/-- the tail from `k = 4` (re-indexed by `j ↦ j+4`) is summable -/
lemma beukersTail4_summable (a : ℚ) (ha3 : 3 ≤ a) : Summable (beukersTail4 a) := by
  classical
  have hfull : Summable (fun k : ℕ => beukersRTerm a k) := by
    simpa [beukersRTerm] using (beukersUV_series_summable a ha3)
  let f : ℕ → ℝ := fun k => beukersRTerm a k
  have hsumf : Summable f := hfull
  have hS := Summable.hasSum hsumf
  let S : ℝ := ∑' k, f k
  let p : ℝ := ∑ i ∈ Finset.range 4, f i
  have hshift : HasSum (fun j : ℕ => f (j + 4)) (S - p) := by
    rw [hasSum_nat_add_iff (f := f) (k := 4)]
    have hsub : (S - p) + p = S := by
      dsimp [S, p]
      ring
    rwa [hsub]
  have hsumtail : Summable (fun j : ℕ => beukersRTerm a (j + 4)) := by
    exact ⟨S - p, hshift⟩
  change Summable (fun j : ℕ => beukersRTerm a (j + 4))
  exact hsumtail

open scoped Topology
open Filter

/-- the Apéry ratio sequence converges in `ℝ` (existence half of the Apéry
limit; the value is `v₃/u₃ + Σ_{k≥4} 1/(k·uₖ·uₖ₋₁)`) -/
theorem beukersUV_apéry_tendsto (a : ℚ) (ha3 : 3 ≤ a) :
    Tendsto (fun N : ℕ => (beukersV a N / beukersU a N : ℝ)) atTop
      (𝓝 ((beukersV a 3 / beukersU a 3 : ℝ) + ∑' j : ℕ, beukersTail4 a j)) := by
  classical
  have ha1 : 1 ≤ a := le_trans (by norm_num) ha3
  have htail : Summable (beukersTail4 a) := beukersTail4_summable a ha3
  have hpart : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, beukersTail4 a j)
      atTop (𝓝 (∑' j : ℕ, beukersTail4 a j)) :=
    (Summable.hasSum htail).tendsto_sum_nat
  have hshift : Tendsto (fun N : ℕ => N - 3) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b + 3, ?_⟩
    intro a0 ha0
    omega
  have hcomp := hpart.comp hshift
  have hev : (fun N : ℕ => (beukersV a N / beukersU a N : ℝ))
      =ᶠ[atTop] (fun N : ℕ => (beukersV a 3 / beukersU a 3 : ℝ) + ∑ j ∈ Finset.range (N - 3), beukersTail4 a j) := by
    change ∀ᶠ N in atTop, (beukersV a N / beukersU a N : ℝ) =
        (beukersV a 3 / beukersU a 3 : ℝ) + ∑ j ∈ Finset.range (N - 3), beukersTail4 a j
    rw [eventually_atTop]
    refine ⟨4, ?_⟩
    intro N hN
    rw [beukersUV_real_telescope a ha1 hN]
  exact Tendsto.congr' hev.symm
    (Filter.Tendsto.const_add ((beukersV a 3 / beukersU a 3 : ℝ)) hcomp)


/-! ## Negative parameters via parity (reduction to `a ≥ 3`)

For the CDT application (`lm = log(1+1/m)`, `a = 1+2m`), negative `m`
means negative `a`; by the parity identities above the *ratio* simply flips
sign: `v_N(-a)/u_N(-a) = -v_N(a)/u_N(a)`, so every statement about the
Apéry ratio at a negative parameter reduces to the positive one
(`|a| ≥ 3`), consistent with
`log((a+1)/(a−1)) = −log((|a|+1)/(|a|−1))` for `a ≤ −3`. -/

/-- the Apéry ratio flips sign under `a ↦ -a` -/
lemma beukers_ratio_neg (a : ℚ) (ha1 : 1 ≤ a) (N : ℕ) :
    beukersV (-a) N / beukersU (-a) N = -(beukersV a N / beukersU a N) := by
  rw [beukersV_neg_mul a N, beukersU_neg_mul a N]
  have huz : beukersU a N ≠ 0 := ne_of_gt (beukersU_pos a ha1 N)
  have hpow : (-1 : ℚ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  field_simp [huz, hpow]
  have hsign : (-1 : ℚ) ^ (N + 1) = -((-1 : ℚ) ^ N) := neg_one_pow_succ_neg_q N
  rw [hsign]
  ring

/-- the same sign flip over the reals -/
lemma beukers_ratio_neg_real (a : ℚ) (ha1 : 1 ≤ a) (N : ℕ) :
    (beukersV (-a) N / beukersU (-a) N : ℝ) = -((beukersV a N / beukersU a N : ℝ)) := by
  have hq := beukers_ratio_neg a ha1 N
  have hc := congrArg (fun x : ℚ => (x : ℝ)) hq
  simpa using hc


/-! ## The inverse-square-root series (seed of the closed form)

`S(x) := Σ_j C(2j,j)·x^j / 4^j` is the formal power series of
`(1 − x)^(−1/2)`; its square is `(1 − x)^(−1)` (equivalently
`S²·(1−x) = 1`), coefficient-wise exactly the central-binomial convolution
`Σ_j C(2j,j)·C(2(n−j),n−j) = 4^n` (Commons
`Commons.Data.Nat.Choose.centralBinom_convolution`, proved via Catalan
numbers).  With the substitution `x ↦ 2a·x − x²` and the rescale
`x ↦ (a²−1)x²·(1−ax)^{−2}` this will yield the closed form of the Beukers
coefficients `u_n(a) = Σ_j C(n,2j)·C(2j,j)·a^{n−2j}·((a²−1)/4)^j` and
therefrom the integrality `u_n(a) ∈ ℤ` for odd integer `a` (see the module
docstring "Roadmap for the next bricks"). -/

/-- `S(x) := Σ_j C(2j,j)·x^j / 4^j`, the formal series of `(1-x)^(-1/2)` -/
def centralSqrtSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun j => (Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j)

/-- coefficient of `S`: `[x^n] S = C(2n,n)/4^n` -/
lemma centralSqrtSeries_coeff (n : ℕ) :
    PowerSeries.coeff n centralSqrtSeries = (Nat.centralBinom n : ℚ) / (4 : ℚ) ^ n := by
  rw [centralSqrtSeries, PowerSeries.coeff_mk]

/-- `[x^n] S² = 1` for every `n` (the central-binomial convolution) -/
lemma centralSqrtSeries_sq_coeff (n : ℕ) : PowerSeries.coeff n (centralSqrtSeries ^ 2) = 1 := by
  have hpow4 : (4 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  calc
    PowerSeries.coeff n (centralSqrtSeries ^ 2)
        = ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k centralSqrtSeries
            * PowerSeries.coeff (n - k) centralSqrtSeries := by
            rw [pow_two, PowerSeries.coeff_mul]
            exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i centralSqrtSeries * PowerSeries.coeff j centralSqrtSeries) n
    _ = ∑ k ∈ Finset.range (n + 1), ((Nat.centralBinom k : ℚ) / (4 : ℚ) ^ k)
            * ((Nat.centralBinom (n - k) : ℚ) / (4 : ℚ) ^ (n - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [centralSqrtSeries_coeff, centralSqrtSeries_coeff]
    _ = ∑ k ∈ Finset.range (n + 1), ((Nat.centralBinom k : ℚ) * (Nat.centralBinom (n - k) : ℚ))
            / (4 : ℚ) ^ n := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have h1 : (4 : ℚ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
            have h2 : (4 : ℚ) ^ (n - k) ≠ 0 := pow_ne_zero (n - k) (by norm_num)
            have hp : (4 : ℚ) ^ k * (4 : ℚ) ^ (n - k) = (4 : ℚ) ^ n := by
              rw [← pow_add]
              congr 1
              omega
            calc
              ((Nat.centralBinom k : ℚ) / (4 : ℚ) ^ k) * ((Nat.centralBinom (n - k) : ℚ) / (4 : ℚ) ^ (n - k))
                  = (Nat.centralBinom k : ℚ) * (Nat.centralBinom (n - k) : ℚ) / ((4 : ℚ) ^ k * (4 : ℚ) ^ (n - k)) := by
                      field_simp [h1, h2]
              _ = (Nat.centralBinom k : ℚ) * (Nat.centralBinom (n - k) : ℚ) / (4 : ℚ) ^ n := by
                      rw [hp]
    _ = ((∑ k ∈ Finset.range (n + 1), (Nat.centralBinom k : ℚ) * (Nat.centralBinom (n - k) : ℚ))
            / (4 : ℚ) ^ n) := by
            rw [← Finset.sum_div]
    _ = ((4 : ℚ) ^ n) / (4 : ℚ) ^ n := by
            rw [Commons.Data.Nat.Choose.centralBinom_convolution n]
    _ = 1 := by
            field_simp [hpow4]

/-- `S² · (1 − X) = 1`, i.e. `S² = (1 − X)^(−1)` -/
lemma centralSqrtSeries_sq_mul_one_sub : centralSqrtSeries ^ 2 * (1 - PowerSeries.X) = 1 := by
  have hmk : centralSqrtSeries ^ 2 = PowerSeries.mk (fun _ : ℕ => (1 : ℚ)) := by
    ext n
    rw [centralSqrtSeries_sq_coeff, PowerSeries.coeff_mk]
  rw [hmk]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ


/-! ## The square-root identity `A(a,x)² · (1 − 2aX + X²) = 1`

`beukersA a` was defined through the 3-term recurrence, and the first-order
ODE (`beukersA_ode`) was proved coefficient-wise.  We now prove the defining
algebraic identity of the paper's display `A(a,x) = (1 − 2ax + x²)^(−1/2)`:

`beukersA_sq_mul`: `(beukersA a)² · (1 − 2a·X + X²) = 1` in `ℚ⟦X⟧`.

Proof: the ODE `Q·A′ + (X − a)·A = 0` (`Q := 1 − 2aX + X²`) implies, by the
Leibniz rule, `(A²·Q)′ = A·(2·A′·Q + A·Q′) = A²·(−2(X−a) + Q′) = 0`, and
`constantCoeff (A²·Q) = 1`; the equality follows from `derivative.ext`
(two series equal iff they have equal derivative and constant term, in
characteristic zero).
-/

open Derivation

/-- `A(a,x)² · (1 − 2a·X + X²) = 1`, i.e. `beukersA a` is the formal inverse
square root of `Q := 1 − 2aX + X²` (paper eq. (beukersA)). -/
lemma beukersA_sq_mul (a : ℚ) :
    (beukersA a) ^ 2 * (1 - C (2 * a) * X + X ^ 2) = (1 : PowerSeries ℚ) := by
  let A : PowerSeries ℚ := beukersA a
  let P : PowerSeries ℚ := 1 - C (2 * a) * X + X ^ 2
  have hder : (PowerSeries.derivative (R := ℚ)) (A ^ 2 * P) = 0 := by
    let DA : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) A
    have hode : P * DA + (X - C a) * A = 0 := by
      dsimp [P, DA, A]
      exact beukersA_ode a
    have hsq : (PowerSeries.derivative (R := ℚ)) (A ^ 2) = (2 : PowerSeries ℚ) * (A * DA) := by
      dsimp [DA]
      rw [Derivation.leibniz_pow]
      simp
    have hdp : (PowerSeries.derivative (R := ℚ)) P = - C (2 * a) + (2 : PowerSeries ℚ) * X := by
      dsimp [P]
      simp
    have hPDA : P * DA = -((X - C a) * A) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hode
    have h2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
      change algebraMap ℚ (PowerSeries ℚ) (2 : ℚ) = C (2 : ℚ)
      rw [PowerSeries.algebraMap_eq]
    have hC2a : C (2 * a) = (2 : PowerSeries ℚ) * C a := by
      calc
        C (2 * a) = C ((2 : ℚ) * a) := by norm_num
        _ = C (2 : ℚ) * C a := map_mul (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) a
        _ = (2 : PowerSeries ℚ) * C a := by rw [← h2]
    calc
      (PowerSeries.derivative (R := ℚ)) (A ^ 2 * P) = (A ^ 2) * ((PowerSeries.derivative (R := ℚ)) P) + P * ((PowerSeries.derivative (R := ℚ)) (A ^ 2)) := by
        rw [Derivation.leibniz]
        simp
      _ = (A ^ 2) * (- C (2 * a) + (2 : PowerSeries ℚ) * X) + P * ((2 : PowerSeries ℚ) * (A * DA)) := by
        rw [hdp, hsq]
      _ = (A ^ 2) * (- C (2 * a) + (2 : PowerSeries ℚ) * X) + (2 : PowerSeries ℚ) * A * (P * DA) := by
        ring
      _ = (A ^ 2) * (- C (2 * a) + (2 : PowerSeries ℚ) * X) - (2 : PowerSeries ℚ) * A * ((X - C a) * A) := by
        rw [hPDA]
        ring
      _ = 0 := by
        rw [hC2a]
        ring
  have hconst : constantCoeff (A ^ 2 * P) = 1 := by
    have hA0 : constantCoeff A = 1 := by
      dsimp [A]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, beukersA_coeff_zero]
    simp [P, hA0]
  apply PowerSeries.derivative.ext (R := ℚ) (f := A ^ 2 * P) (g := (1 : PowerSeries ℚ))
  · rw [hder]
    simp
  · simpa using hconst

/-! ## The closed form of `u_n`: structural decomposition of `A(a,x)`

`beukersA_sq_mul` identifies `A(a,x)` as the formal inverse square root of
`Q(a) := 1 − 2aX + X²`.  This section proves the *structural decomposition*
of the paper's binomial expansion

`A(a,x) = (1 − ax)^(−1) · [1 − (a²−1)·x²·(1−ax)^(−2)]^(−1/2)`

as an identity of formal power series:

`beukersA_eq_beukersG`: `A(a) = W(a)·T(a)` where
`W(a) = (1−aX)^(−1)`, `Z(a) = (a²−1)·X²·W(a)²`, and
`T(a) = S∘Z(a)` with `S` the inverse-square-root series
(`centralSqrtSeries`, `S²·(1−X) = 1`).  Steps:

* `centralSqrtSeries_subst_sq_mul` — substitution preserves
  `S²·(1−Y) = 1`: `T²·(1−Z) = 1`;
* `beukersQ_eq` — `Q = (1−aX)²·(1−Z)` (the algebraic factorization
  `(1−aX)² − (a²−1)X²`);
* `beukersG_sq_mul` — with `G := W·T`, `G²·Q = 1`;
* `beukersA_eq_beukersG` — since also `A²·Q = 1` and both series have
  constant term `1`, the difference `A − G` is annihilated by the unit
  `(A+G)·Q`, hence `A = G` (power series over `ℚ` form an integral
  domain; `A + G` has constant term `2`).

The next section reads off the coefficients (`u_n(a) =
Σ_j C(2j,j)·C(n,2j)·a^{n−2j}·((a²−1)/4)^j`, the paper's binomial closed
form) from this decomposition, giving the integrality `u_n(a) ∈ ℤ` for
odd integer `a`.
-/

/-- `Q(a) = 1 − 2a·X + X²`, the quadratic whose inverse square root is `A(a)`. -/
def beukersQ (a : ℚ) : PowerSeries ℚ := 1 - C (2 * a) * X + X ^ 2

/-- `W(a) = (1 − aX)^(−1) = Σ_k a^k X^k`. -/
def beukersW (a : ℚ) : PowerSeries ℚ := ((1 : PowerSeries ℚ) - C a * X)⁻¹

/-- `Z(a) = (a²−1)·X²·W(a)²`. -/
def beukersZ (a : ℚ) : PowerSeries ℚ := C (a * a - 1) * X ^ 2 * (beukersW a) ^ 2

/-- `T(a) = S∘Z(a)`, the formal inverse square root of `(1 − Z(a))`. -/
def beukersT (a : ℚ) : PowerSeries ℚ := centralSqrtSeries.subst (beukersZ a)

/-- `G(a) = W(a)·T(a)`. -/
def beukersG (a : ℚ) : PowerSeries ℚ := beukersW a * beukersT a

/-- `W(a)·(1 − aX) = 1`. -/
lemma beukersW_mul_one_sub (a : ℚ) : beukersW a * (1 - C a * X) = 1 := by
  dsimp [beukersW]
  rw [PowerSeries.inv_mul_cancel]
  simp

/-- `(1 − aX)·W(a) = 1`. -/
lemma one_sub_mul_beukersW (a : ℚ) : (1 - C a * X) * beukersW a = 1 := by
  dsimp [beukersW]
  rw [PowerSeries.mul_inv_cancel]
  simp

/-- `Z(a)` has zero constant term, so it may be substituted into a power series. -/
lemma beukersZ_hasSubst (a : ℚ) : PowerSeries.HasSubst (beukersZ a) := by
  unfold beukersZ
  apply PowerSeries.HasSubst.mul_left
  apply PowerSeries.HasSubst.mul_right
  exact PowerSeries.HasSubst.X_pow (n := 2) (by norm_num)

/-- Substituting `Z` into the identity `S²·(1−X) = 1` gives `T²·(1−Z) = 1`. -/
lemma centralSqrtSeries_subst_sq_mul (Z : PowerSeries ℚ) (hZ : PowerSeries.HasSubst Z) :
    (centralSqrtSeries.subst Z) ^ 2 * (1 - Z) = 1 := by
  have h := centralSqrtSeries_sq_mul_one_sub
  have hsub := congrArg (fun y : PowerSeries ℚ => y.subst Z) h
  rw [PowerSeries.subst_mul hZ] at hsub
  rw [PowerSeries.subst_pow hZ] at hsub
  rw [PowerSeries.subst_sub hZ, PowerSeries.subst_X hZ] at hsub
  have h1 : (1 : PowerSeries ℚ).subst Z = 1 := by
    rw [← PowerSeries.coe_substAlgHom hZ]
    simp
  rw [h1] at hsub
  simpa using hsub

/-- `C (2a) = 2·C a` in `ℚ⟦X⟧`. -/
lemma C_two_mul (a : ℚ) : C (2 * a) = (2 : PowerSeries ℚ) * C a := by
  have h2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    change algebraMap ℚ (PowerSeries ℚ) (2 : ℚ) = C (2 : ℚ)
    rw [PowerSeries.algebraMap_eq]
  calc
    C (2 * a) = C ((2 : ℚ) * a) := by norm_num
    _ = C (2 : ℚ) * C a := map_mul (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) a
    _ = (2 : PowerSeries ℚ) * C a := by rw [← h2]

/-- `Q(a) = (1−aX)²·(1−Z(a))`, the algebraic factorization of
`(1−aX)² − (a²−1)X²`. -/
lemma beukersQ_eq (a : ℚ) : beukersQ a = (1 - C a * X) ^ 2 * (1 - beukersZ a) := by
  have h2a : C (2 * a) = (2 : PowerSeries ℚ) * C a := C_two_mul a
  have hCaa : C (a * a) = C a * C a := by
    exact map_mul (PowerSeries.C : ℚ →+* PowerSeries ℚ) a a
  have hC1 : C (1 : ℚ) = (1 : PowerSeries ℚ) := by
    exact map_one (PowerSeries.C : ℚ →+* PowerSeries ℚ)
  have hCmm : C (a * a - 1) = C a * C a - 1 := by
    calc
      C (a * a - 1) = C (a * a) - C (1 : ℚ) := by rw [map_sub]
      _ = C a * C a - 1 := by rw [hCaa, hC1]
  have hz : (1 - C a * X) * beukersW a = 1 := one_sub_mul_beukersW a
  calc
    beukersQ a = 1 - C (2 * a) * X + X ^ 2 := rfl
    _ = 1 - ((2 : PowerSeries ℚ) * C a) * X + X ^ 2 := by rw [h2a]
    _ = (1 - C a * X) ^ 2 - (C a * C a - 1) * X ^ 2 := by ring
    _ = (1 - C a * X) ^ 2 - C (a * a - 1) * X ^ 2 := by rw [← hCmm]
    _ = (1 - C a * X) ^ 2 - C (a * a - 1) * X ^ 2 * ((1 - C a * X) * beukersW a) ^ 2 := by
        rw [hz]
        ring
    _ = (1 - C a * X) ^ 2 - C (a * a - 1) * X ^ 2 * ((1 - C a * X) ^ 2 * (beukersW a) ^ 2) := by
        congr 1
        ring
    _ = (1 - C a * X) ^ 2 * (1 - C (a * a - 1) * X ^ 2 * (beukersW a) ^ 2) := by ring
    _ = (1 - C a * X) ^ 2 * (1 - beukersZ a) := rfl

/-- `G(a)²·Q(a) = 1` — `G` is a formal inverse square root of `Q`, like `A`. -/
lemma beukersG_sq_mul (a : ℚ) : (beukersG a) ^ 2 * beukersQ a = 1 := by
  have hT : (beukersT a) ^ 2 * (1 - beukersZ a) = 1 := by
    exact centralSqrtSeries_subst_sq_mul (beukersZ a) (beukersZ_hasSubst a)
  have hW : (beukersW a) ^ 2 * (1 - C a * X) ^ 2 = 1 := by
    have hw := beukersW_mul_one_sub a
    calc
      (beukersW a) ^ 2 * (1 - C a * X) ^ 2 = ((beukersW a) * (1 - C a * X)) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [hw]
      _ = 1 := by norm_num
  calc
    (beukersG a) ^ 2 * beukersQ a = (beukersW a) ^ 2 * ((beukersT a) ^ 2) * ((1 - C a * X) ^ 2 * (1 - beukersZ a)) := by
        rw [beukersQ_eq]
        unfold beukersG
        ring
    _ = ((beukersW a) ^ 2 * (1 - C a * X) ^ 2) * ((beukersT a) ^ 2 * (1 - beukersZ a)) := by ring
    _ = 1 * 1 := by rw [hW, hT]
    _ = 1 := by norm_num

/-- constant term of `G(a)` is `1`. -/
lemma beukersG_coeff_zero (a : ℚ) : PowerSeries.coeff 0 (beukersG a) = 1 := by
  unfold beukersG
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_mul (PowerSeries.constantCoeff (R := ℚ))]
  have hW0 : PowerSeries.constantCoeff (beukersW a) = 1 := by
    unfold beukersW
    simp
  have hT0c : PowerSeries.constantCoeff (beukersT a) = 1 := by
    have hT0 : PowerSeries.coeff 0 (beukersT a) = 1 := by
      unfold beukersT
      rw [PowerSeries.coeff_subst' (beukersZ_hasSubst a)]
      have hZ0 : PowerSeries.constantCoeff (beukersZ a) = 0 := by
        unfold beukersZ
        simp
      have hterm0 : ∀ d : ℕ, d ≠ 0 → PowerSeries.coeff d centralSqrtSeries • PowerSeries.coeff 0 ((beukersZ a) ^ d) = 0 := by
        intro d hd
        have hp : PowerSeries.coeff 0 ((beukersZ a) ^ d) = 0 := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
            map_pow (PowerSeries.constantCoeff (R := ℚ)), hZ0, zero_pow hd]
        simp [hp]
      rw [finsum_eq_single (fun d : ℕ => PowerSeries.coeff d centralSqrtSeries • PowerSeries.coeff 0 ((beukersZ a) ^ d)) 0 hterm0]
      simp [centralSqrtSeries_coeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hT0
  rw [hW0, hT0c]
  simp

/-- **Structural decomposition**: `A(a,x) = (1−ax)^(−1)·S(Z(a))` where
`S` is the inverse-square-root series and `Z(a) = (a²−1)x²(1−ax)^(−2)`
(equivalently `A(a,x) = (1−ax)^(−1)·[1 − (a²−1)x²(1−ax)^(−2)]^(−1/2)`;
this is the identity underlying the binomial closed form of `u_n`). -/
lemma beukersA_eq_beukersG (a : ℚ) : beukersA a = beukersG a := by
  have hA : (beukersA a) ^ 2 * beukersQ a = 1 := by
    simpa [beukersQ] using (beukersA_sq_mul a)
  have hG : (beukersG a) ^ 2 * beukersQ a = 1 := beukersG_sq_mul a
  have hA0c : PowerSeries.constantCoeff (beukersA a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, beukersA_coeff_zero]
  have hG0c : PowerSeries.constantCoeff (beukersG a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, beukersG_coeff_zero]
  have hprod : ((beukersA a) - (beukersG a)) * ((beukersA a) + (beukersG a)) * beukersQ a = 0 := by
    calc
      ((beukersA a) - (beukersG a)) * ((beukersA a) + (beukersG a)) * beukersQ a
          = ((beukersA a) ^ 2 - (beukersG a) ^ 2) * beukersQ a := by ring
      _ = (beukersA a) ^ 2 * beukersQ a - (beukersG a) ^ 2 * beukersQ a := by ring
      _ = 1 - 1 := by rw [hA, hG]
      _ = 0 := by norm_num
  have hsumcc : PowerSeries.constantCoeff ((beukersA a) + (beukersG a)) = 2 := by
    simp [hA0c, hG0c]
    norm_num
  have hsum : (beukersA a) + (beukersG a) ≠ 0 := by
    intro hz
    have hc := congrArg PowerSeries.constantCoeff hz
    rw [hsumcc] at hc
    norm_num at hc
  have hfac : ((beukersA a) + (beukersG a)) * beukersQ a ≠ 0 := by
    intro hz
    have hc := congrArg PowerSeries.constantCoeff hz
    have hcc : PowerSeries.constantCoeff (((beukersA a) + (beukersG a)) * beukersQ a) = 2 := by
      have hQcc : PowerSeries.constantCoeff (beukersQ a) = 1 := by
        unfold beukersQ
        simp
      rw [map_mul]
      rw [hsumcc, hQcc]
      norm_num
    rw [hcc] at hc
    norm_num at hc
  have hprod' : ((beukersA a) - (beukersG a)) * (((beukersA a) + (beukersG a)) * beukersQ a) = 0 := by
    simpa [mul_assoc] using hprod
  have hdiff : (beukersA a) - (beukersG a) = 0 := by
    rcases mul_eq_zero.mp hprod' with h | h
    · exact h
    · exact False.elim (hfac h)
  exact sub_eq_zero.mp hdiff

/-! ## The closed form of `u_n(a)` (binomial closed form of the coefficients)

The structural decomposition (`beukersA_eq_beukersG`) now yields the paper's
binomial closed form

`u_n(a) = Σ_{2j ≤ n} C(2j,j)·C(n,2j)·a^{n−2j}·((a²−1)/4)^j`,

from which the integrality `u_n(a) ∈ ℤ` for odd integer `a` follows.  The
route: with `T = S∘Z`, `G = W·T`, and the finite truncation
`beukersTrunc a N := Σ_{d<N} c_d·Z^d`, `c_d := C(2d,d)/4^d`,

* `beukersT_coeff_eq_trunc` — `T` and its truncation agree in all
  coefficients up to `n` (coefficients of `Z^d` with `2d > n` vanish);
* `coeff_beukersG_eq_coeff_W_mul_trunc` — multiplying by `W` preserves
  that agreement at degree `n`;
* `coeff_beukersW_mul_trunc` — the coefficient of `W` times the
  truncation is the finite sum above (per-term via
  `coeff_beukersW_mul_Z_pow_closed` and the Commons coefficient formula
  `coeff_inv_one_sub_C_mul_pow` for `(1−aX)^(−e)`).

The helper coefficient lemmas `coeff_X_pow_mul_of_lt`, `coeff_X_pow_mul_shift`,
`beukersZ_pow_eq`, `coeff_beukersZ_pow_of_lt`, `coeff_beukersW_mul_Z_pow`
record the exact shapes used.
-/
lemma beukersZ_pow_eq (a : ℚ) (d : ℕ) :
    (beukersZ a) ^ d = (C (a * a - 1) : PowerSeries ℚ) ^ d * (X ^ 2) ^ d * ((beukersW a) ^ 2) ^ d := by
  unfold beukersZ
  rw [mul_pow, mul_pow]

lemma coeff_X_pow_mul_of_lt {t : ℕ} (f : PowerSeries ℚ) {m : ℕ} (hm : m < t) :
    PowerSeries.coeff m (X ^ t * f) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hXt : PowerSeries.coeff p.1 (X ^ t) * PowerSeries.coeff p.2 f = 0 := by
    rw [PowerSeries.coeff_X_pow]
    have hp1ne : p.1 ≠ t := by
      intro hEq
      omega
    simp [hp1ne]
  exact hXt

lemma coeff_beukersZ_pow_of_lt (a : ℚ) {j d : ℕ} (h : j < 2 * d) :
    PowerSeries.coeff j ((beukersZ a) ^ d) = 0 := by
  have hz := beukersZ_pow_eq a d
  have hC : (C (a * a - 1) : PowerSeries ℚ) ^ d = C ((a * a - 1) ^ d) := by
    exact (map_pow (PowerSeries.C : ℚ →+* PowerSeries ℚ) (a * a - 1) d).symm
  have hx : (X ^ 2 : PowerSeries ℚ) ^ d = X ^ (2 * d) := by
    exact (pow_mul X 2 d).symm
  rw [hz]
  rw [hC]
  rw [mul_assoc]
  rw [PowerSeries.coeff_C_mul]
  rw [hx]
  rw [coeff_X_pow_mul_of_lt (((beukersW a) ^ 2) ^ d) h]
  ring

lemma coeff_X_pow_mul_shift (g : PowerSeries ℚ) {t m : ℕ} (h : t ≤ m) :
    PowerSeries.coeff m (X ^ t * g) = PowerSeries.coeff (m - t) g := by
  calc
    PowerSeries.coeff m (X ^ t * g) = PowerSeries.coeff ((m - t) + t) (X ^ t * g) := by
        exact congrArg (fun k : ℕ => PowerSeries.coeff k (X ^ t * g)) (Nat.sub_add_cancel h).symm
    _ = PowerSeries.coeff (m - t) g := by
        exact PowerSeries.coeff_X_pow_mul g t (m - t)

lemma coeff_beukersW_mul_Z_pow {a : ℚ} {n d : ℕ} (hd : 2 * d ≤ n) :
    PowerSeries.coeff n (beukersW a * (beukersZ a) ^ d) =
      ((a * a - 1) ^ d : ℚ) * PowerSeries.coeff (n - 2 * d) ((beukersW a) ^ (2 * d + 1)) := by
  have hz := beukersZ_pow_eq a d
  have hC : (C (a * a - 1) : PowerSeries ℚ) ^ d = C ((a * a - 1) ^ d) := by
    exact (map_pow (PowerSeries.C : ℚ →+* PowerSeries ℚ) (a * a - 1) d).symm
  have hx : (X ^ 2 : PowerSeries ℚ) ^ d = X ^ (2 * d) := by
    exact (pow_mul X 2 d).symm
  have hw : ((beukersW a) ^ 2) ^ d * beukersW a = (beukersW a) ^ (2 * d + 1) := by
    have h1 : ((beukersW a) ^ 2) ^ d = (beukersW a) ^ (2 * d) := by
      exact (pow_mul (beukersW a) 2 d).symm
    rw [h1]
    rw [pow_succ]
  calc
    PowerSeries.coeff n (beukersW a * (beukersZ a) ^ d)
        = PowerSeries.coeff n (beukersW a * ((C (a * a - 1)) ^ d * (X ^ 2) ^ d * ((beukersW a) ^ 2) ^ d)) := by
            rw [hz]
    _ = PowerSeries.coeff n ((C (a * a - 1)) ^ d * (X ^ 2) ^ d * (((beukersW a) ^ 2) ^ d * beukersW a)) := by
            congr 1
            ring
    _ = PowerSeries.coeff n ((C (a * a - 1)) ^ d * (X ^ 2) ^ d * (beukersW a) ^ (2 * d + 1)) := by
            rw [hw]
    _ = PowerSeries.coeff n (C ((a * a - 1) ^ d) * (X ^ 2) ^ d * (beukersW a) ^ (2 * d + 1)) := by
            rw [hC]
    _ = PowerSeries.coeff n (C ((a * a - 1) ^ d) * X ^ (2 * d) * (beukersW a) ^ (2 * d + 1)) := by
            rw [hx]
    _ = ((a * a - 1) ^ d : ℚ) * PowerSeries.coeff (n - 2 * d) ((beukersW a) ^ (2 * d + 1)) := by
            rw [mul_assoc]
            rw [PowerSeries.coeff_C_mul]
            rw [coeff_X_pow_mul_shift (beukersW a ^ (2 * d + 1)) hd]


def beukersTrunc (a : ℚ) (N : ℕ) : PowerSeries ℚ :=
  ∑ d ∈ Finset.range N, C ((Nat.centralBinom d : ℚ) / (4 : ℚ) ^ d) * (beukersZ a) ^ d

lemma coeff_finset_sum {ι : Type*} {s : Finset ι} (f : ι → PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (∑ i ∈ s, f i) = ∑ i ∈ s, PowerSeries.coeff k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ih]

-- coefficient of the truncation at degree j (finite sum, per-term C-coefficient extraction)
lemma coeff_trunc (a : ℚ) (N j : ℕ) :
    PowerSeries.coeff j (beukersTrunc a N) =
      ∑ d ∈ Finset.range N, ((Nat.centralBinom d : ℚ) / (4 : ℚ) ^ d) * PowerSeries.coeff j ((beukersZ a) ^ d) := by
  unfold beukersTrunc
  rw [coeff_finset_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [PowerSeries.coeff_C_mul]

-- T's coefficient equals the truncated sum, up to degree n
lemma beukersT_coeff_eq_trunc (a : ℚ) (n j : ℕ) (hj : j ≤ n) :
    PowerSeries.coeff j (beukersT a) = PowerSeries.coeff j (beukersTrunc a (n / 2 + 1)) := by
  unfold beukersT
  rw [PowerSeries.coeff_subst' (beukersZ_hasSubst a)]
  -- LHS is now finsum d : coeff d centralSqrtSeries • coeff j ((beukersZ a)^d)
  let F : ℕ → ℚ := fun d => ((Nat.centralBinom d : ℚ) / (4 : ℚ) ^ d) * PowerSeries.coeff j ((beukersZ a) ^ d)
  have hF : (fun d : ℕ => PowerSeries.coeff d centralSqrtSeries • PowerSeries.coeff j ((beukersZ a) ^ d)) = F := by
    funext d
    unfold F
    rw [centralSqrtSeries_coeff]
    simp
  rw [hF]
  -- reduce finsum to the finite sum over d < N, since coeff j (Z^d) = 0 for 2d > n ≥ j
  have hN : ∀ d, d ≥ n / 2 + 1 → PowerSeries.coeff j ((beukersZ a) ^ d) = 0 := by
    intro d hd
    apply coeff_beukersZ_pow_of_lt a
    have h2 : j < 2 * d := by
      -- 2d ≥ 2(n/2+1) > n ≥ j
      have h1 : 2 * (n / 2 + 1) ≤ 2 * d := by
        exact Nat.mul_le_mul_left 2 hd
      have hgt : n < 2 * (n / 2 + 1) := by omega
      omega
    exact h2
  have hs : Function.support F ⊆ ↑(Finset.range (n / 2 + 1)) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hnot
    have hdge : n / 2 + 1 ≤ d := by omega
    have hz : PowerSeries.coeff j ((beukersZ a) ^ d) = 0 := hN d hdge
    unfold F at hd
    simp [hz] at hd
  rw [finsum_eq_sum_of_support_subset F hs]
  -- match with the truncation's coefficient
  have htr : PowerSeries.coeff j (beukersTrunc a (n / 2 + 1)) = ∑ d ∈ Finset.range (n / 2 + 1), F d := by
    rw [coeff_trunc]
  exact htr.symm



-- coeff n (W·T) equals coeff n (W·trunc) because the tail has no coefficients ≤ n
lemma coeff_beukersG_eq_coeff_W_mul_trunc (a : ℚ) (n : ℕ) :
    PowerSeries.coeff n (beukersG a) = PowerSeries.coeff n (beukersW a * beukersTrunc a (n / 2 + 1)) := by
  unfold beukersG
  let tail : PowerSeries ℚ := beukersT a - beukersTrunc a (n / 2 + 1)
  have htail0 : ∀ j : ℕ, j ≤ n → PowerSeries.coeff j tail = 0 := by
    intro j hj
    unfold tail
    simp [beukersT_coeff_eq_trunc a n j hj]
  have htailW : PowerSeries.coeff n (beukersW a * tail) = 0 := by
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hp2le : p.2 ≤ n := by omega
    have hz : PowerSeries.coeff p.2 tail = 0 := htail0 p.2 hp2le
    simp [hz]
  calc
    PowerSeries.coeff n (beukersW a * beukersT a)
        = PowerSeries.coeff n (beukersW a * (beukersTrunc a (n / 2 + 1) + tail)) := by
            congr 1
            unfold tail
            ring
    _ = PowerSeries.coeff n (beukersW a * beukersTrunc a (n / 2 + 1)) + PowerSeries.coeff n (beukersW a * tail) := by
            rw [mul_add]
            simp
    _ = PowerSeries.coeff n (beukersW a * beukersTrunc a (n / 2 + 1)) := by
            rw [htailW]
            ring


-- coefficient of W·Z^d in fully expanded closed-form shape
lemma coeff_beukersW_mul_Z_pow_closed {a : ℚ} {n d : ℕ} (hd : 2 * d ≤ n) :
    PowerSeries.coeff n (beukersW a * (beukersZ a) ^ d) =
      (n.choose (2 * d) : ℚ) * a ^ (n - 2 * d) * (a * a - 1) ^ d := by
  rw [coeff_beukersW_mul_Z_pow hd]
  have hW : PowerSeries.coeff (n - 2 * d) ((beukersW a) ^ (2 * d + 1)) =
      ((Nat.choose ((n - 2 * d) + 2 * d) (2 * d) : ℕ) : ℚ) * a ^ (n - 2 * d) := by
    simpa [beukersW] using
      (Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul_pow ℚ a (n - 2 * d) (2 * d))
  rw [hW]
  have hsum : (n - 2 * d) + 2 * d = n := Nat.sub_add_cancel hd
  rw [hsum]
  ring

-- the coefficient of W(a)·(truncation of T) at degree n is the closed form
lemma coeff_beukersW_mul_trunc (a : ℚ) (n : ℕ) :
    PowerSeries.coeff n (beukersW a * beukersTrunc a (n / 2 + 1)) =
      ∑ j ∈ Finset.range (n / 2 + 1),
        (Nat.centralBinom j : ℚ) * (n.choose (2 * j) : ℚ) * a ^ (n - 2 * j) * ((a * a - 1) / 4) ^ j := by
  unfold beukersTrunc
  rw [Finset.mul_sum]
  rw [coeff_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h2j : 2 * j ≤ n := by
    have hjl : j ≤ n / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h2 : 2 * j ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hjl
    exact le_trans h2 (Nat.mul_div_le n 2)
  have hrot : beukersW a * (C ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * (beukersZ a) ^ j) =
      C ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * (beukersW a * (beukersZ a) ^ j) := by
    ring
  have h4 : (4 : ℚ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
  calc
    PowerSeries.coeff n (beukersW a * (C ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * (beukersZ a) ^ j))
        = PowerSeries.coeff n (C ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * (beukersW a * (beukersZ a) ^ j)) := by
            rw [hrot]
    _ = ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * PowerSeries.coeff n (beukersW a * (beukersZ a) ^ j) := by
            rw [PowerSeries.coeff_C_mul]
    _ = ((Nat.centralBinom j : ℚ) / (4 : ℚ) ^ j) * ((n.choose (2 * j) : ℚ) * a ^ (n - 2 * j) * (a * a - 1) ^ j) := by
            rw [coeff_beukersW_mul_Z_pow_closed h2j]
    _ = (Nat.centralBinom j : ℚ) * (n.choose (2 * j) : ℚ) * a ^ (n - 2 * j) * ((a * a - 1) / 4) ^ j := by
            rw [div_pow]
            field_simp [h4]

-- the closed form of the Beukers coefficients
lemma beukersU_closed (a : ℚ) (n : ℕ) :
    beukersU a n =
      ∑ j ∈ Finset.range (n / 2 + 1),
        (Nat.centralBinom j : ℚ) * (n.choose (2 * j) : ℚ) * a ^ (n - 2 * j) * ((a * a - 1) / 4) ^ j := by
  rw [← beukersA_coeff]
  rw [beukersA_eq_beukersG]
  rw [coeff_beukersG_eq_coeff_W_mul_trunc]
  exact coeff_beukersW_mul_trunc a n

/-! ## Arithmetic: `u_n(a) ∈ ℤ` for odd integer `a`

With the closed form in hand, the integrality claim of the paper
(`A(a,x) ∈ ℤ[[x]]` for odd `a`, §"Products of two logarithms") reduces to
the elementary fact that `(a²−1)/4 ∈ ℤ` for odd `a`:  writing the odd
integer `a` as `2k+1`, `(a²−1)/4 = k(k+1)`.

* `exists_int_sq_sub_one_div_four` — the integer `(a²−1)/4`;
* `beukersU_int_of_odd` — `∃ t : ℤ, (t:ℚ) = u_n(a)` for odd `a`: each
  summand of the closed form is the cast of the integer
  `C(2j,j)·C(n,2j)·a^{n−2j}·c^j`.
-/

/-- for an odd integer `a`, the rational `(a²−1)/4` is an integer
(explicitly `k(k+1)` for `a = 2k+1`). -/
lemma exists_int_sq_sub_one_div_four (z : ℤ) (hz : Odd z) :
    ∃ c : ℤ, (c : ℚ) = (((z : ℚ) * (z : ℚ)) - 1) / 4 := by
  obtain ⟨k, hk⟩ := hz
  let c : ℤ := k * (k + 1)
  have hzint : z * z - 1 = 4 * (k * (k + 1)) := by
    rw [hk]
    ring
  refine ⟨c, ?_⟩
  dsimp [c]
  calc
    ((k * (k + 1) : ℤ) : ℚ) = ((((4 * (k * (k + 1))) : ℤ)) : ℚ) / 4 := by
        have hcast : ((((4 * (k * (k + 1))) : ℤ)) : ℚ) = (4 : ℚ) * ((k * (k + 1) : ℤ) : ℚ) := by
          rw [Int.cast_mul]
          norm_num
        rw [hcast]
        ring
    _ = (((z * z - 1 : ℤ)) : ℚ) / 4 := by
        rw [← congrArg (fun t : ℤ => (t : ℚ)) hzint]
    _ = (((z : ℚ) * (z : ℚ)) - 1) / 4 := by
        rw [Int.cast_sub, Int.cast_mul]
        norm_num

/-- **Integrality of the Beukers coefficients**: for odd integer `a`, the
coefficient `u_n(a)` of `A(a,x) = (1 − 2ax + x²)^(−1/2)` is an integer.
This is the coefficient half of the paper's claim `A(a,x) ∈ ℤ[[x]]` for
odd `a`. -/
lemma beukersU_int_of_odd (z : ℤ) (hz : Odd z) (n : ℕ) :
    ∃ t : ℤ, (t : ℚ) = beukersU (z : ℚ) n := by
  obtain ⟨c, hc⟩ := exists_int_sq_sub_one_div_four z hz
  rw [beukersU_closed]
  refine ⟨∑ j ∈ Finset.range (n / 2 + 1),
      (Nat.centralBinom j : ℤ) * (n.choose (2 * j) : ℤ) * z ^ (n - 2 * j) * c ^ j, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    ((((Nat.centralBinom j : ℤ) * (n.choose (2 * j) : ℤ) * z ^ (n - 2 * j) * c ^ j) : ℤ) : ℚ)
        = (Nat.centralBinom j : ℚ) * (n.choose (2 * j) : ℚ) * (z : ℚ) ^ (n - 2 * j) * (c : ℚ) ^ j := by
            norm_num [Int.cast_mul, Int.cast_pow]
    _ = (Nat.centralBinom j : ℚ) * (n.choose (2 * j) : ℚ) * (z : ℚ) ^ (n - 2 * j) * (((z : ℚ) * (z : ℚ) - 1) / 4) ^ j := by
            rw [hc]

/-! ## The companion identity `H(a,x) = A(a,x)·∫₀ˣ A(a,t) dt`

The companion series `beukersH a` (coefficients `v_n`, defined by the same
recurrence as `u` with `v₀ = 0`, `v₁ = 1`) is the unique solution of the
inhomogeneous first-order ODE `Q·H′ + (X−a)·H = 1` with zero constant term.
This section proves the *companion identity*

`beukersH_eq_A_mul_int`: `H = A·W`, where `W = ∫₀ˣ A` is the formal
antiderivative of `A` vanishing at `0` (`beukersInt a`, coefficients
`w_k = u_{k−1}/k` for `k ≥ 1`; `beukersInt_derivative`: `W′ = A`).

Route:

* `beukersA_mul_int_ode` — `C := A·W` satisfies the inhomogeneous ODE
  (`Q·C′ + (X−a)C = Q·A² = 1` by the ODE for `A` and `beukersA_sq_mul`);
* `coeff_ode_hom_zero` / `coeff_ode_hom_succ` — the coefficient equation of
  the homogeneous ODE `Q·f′ + (X−a)f = 0` at degrees `0` and `n+1`;
* `ode_homogeneous_eq_zero_of_zero` — a series with zero constant term
  satisfying the homogeneous ODE is zero (coefficient induction via the
  second-order recurrence the ODE forces);
* `beukersH_eq_A_mul_int` — `H` and `A·W` both solve the inhomogeneous
  ODE and have zero constant term, so their difference is zero.

The coefficient read-off `v_n = Σ_{j=1}^{n} u_{n−j}·u_{j−1}/j` is the
basis for the denominator claim `[1,…,n]·v_n(a) ∈ ℤ` for odd `a`.
-/
/-- formal antiderivative `W(a) = Σ_{k≥1} u_{k−1}(a)·X^k / k`, `W(0)=0`, `W′ = A` -/
def beukersInt (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => if k = 0 then 0 else beukersU a (k - 1) / (k : ℚ))

lemma beukersInt_derivative (a : ℚ) : (PowerSeries.derivative (R := ℚ)) (beukersInt a) = beukersA a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative]
  unfold beukersInt beukersA
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  -- coeff (n+1) of W = u_n/(n+1) if n+1 ≠ 0: k = n+1
  have hk : n + 1 ≠ 0 := by omega
  rw [if_neg hk]
  -- u ((n+1)−1)/(n+1) * (n+1) = u n
  have hsub : (n + 1) - 1 = n := by omega
  rw [hsub]
  have hnz : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp [hnz]
  rw [Nat.cast_add]
  ring


-- C := A·W satisfies the inhomogeneous ODE with RHS 1
lemma beukersA_mul_int_ode (a : ℚ) :
    beukersQ a * (PowerSeries.derivative (R := ℚ)) (beukersA a * beukersInt a)
      + (X - C a) * (beukersA a * beukersInt a) = 1 := by
  let A : PowerSeries ℚ := beukersA a
  let W : PowerSeries ℚ := beukersInt a
  let Q : PowerSeries ℚ := beukersQ a
  have hode : Q * (PowerSeries.derivative (R := ℚ)) A + (X - C a) * A = 0 := by
    dsimp [Q, A]
    exact beukersA_ode a
  have hsq : A ^ 2 * Q = 1 := by
    dsimp [A, Q]
    exact beukersA_sq_mul a
  have hW : (PowerSeries.derivative (R := ℚ)) W = A := by
    dsimp [W, A]
    exact beukersInt_derivative a
  calc
    Q * (PowerSeries.derivative (R := ℚ)) (A * W) + (X - C a) * (A * W)
        = Q * (A * (PowerSeries.derivative (R := ℚ)) W + W * (PowerSeries.derivative (R := ℚ)) A) + (X - C a) * (A * W) := by
            rw [Derivation.leibniz]
            simp
    _ = Q * (A * A + W * (PowerSeries.derivative (R := ℚ)) A) + (X - C a) * (A * W) := by
            rw [hW]
    _ = Q * A ^ 2 + (Q * (PowerSeries.derivative (R := ℚ)) A) * W + (X - C a) * (A * W) := by ring
    _ = Q * A ^ 2 - ((X - C a) * A) * W + (X - C a) * (A * W) := by
            have hQDA : Q * (PowerSeries.derivative (R := ℚ)) A = -((X - C a) * A) := by
              rw [eq_neg_iff_add_eq_zero]
              exact hode
            rw [hQDA]
            ring
    _ = Q * A ^ 2 := by ring
    _ = 1 := by
            rw [← hsq]
            ring


lemma coeff_ode_hom_zero (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (beukersQ a * (PowerSeries.derivative (R := ℚ) f) + (X - C a) * f)
      = PowerSeries.coeff 1 f - a * PowerSeries.coeff 0 f := by
  have hsplit : beukersQ a * (PowerSeries.derivative (R := ℚ) f) + (X - C a) * f
      = (PowerSeries.derivative (R := ℚ) f) - C (2 * a) * (X * PowerSeries.derivative (R := ℚ) f) + X ^ 2 * PowerSeries.derivative (R := ℚ) f
          + X * f - C a * f := by
    unfold beukersQ
    ring
  rw [hsplit]
  have h1 : PowerSeries.coeff 0 (PowerSeries.derivative (R := ℚ) f) = PowerSeries.coeff 1 f := by
    rw [PowerSeries.coeff_derivative]
    ring
  have h2 : PowerSeries.coeff 0 (C (2 * a) * (X * PowerSeries.derivative (R := ℚ) f)) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp
  have h3 : PowerSeries.coeff 0 (X ^ 2 * PowerSeries.derivative (R := ℚ) f) = 0 := by simp
  have h4 : PowerSeries.coeff 0 (X * f) = 0 := by simp
  have h5 : PowerSeries.coeff 0 (C a * f) = a * PowerSeries.coeff 0 f := by
    exact PowerSeries.coeff_C_mul 0 f a
  have hd : PowerSeries.coeff 0 ((PowerSeries.derivative (R := ℚ) f) - C (2 * a) * (X * PowerSeries.derivative (R := ℚ) f)
        + X ^ 2 * PowerSeries.derivative (R := ℚ) f + X * f - C a * f)
      = PowerSeries.coeff 0 (PowerSeries.derivative (R := ℚ) f)
          - PowerSeries.coeff 0 (C (2 * a) * (X * PowerSeries.derivative (R := ℚ) f))
          + PowerSeries.coeff 0 (X ^ 2 * PowerSeries.derivative (R := ℚ) f)
          + PowerSeries.coeff 0 (X * f) - PowerSeries.coeff 0 (C a * f) := by
    simp
  rw [hd, h1, h2, h3, h4, h5]
  ring

lemma coeff_ode_hom_succ (a : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (beukersQ a * (PowerSeries.derivative (R := ℚ) f) + (X - C a) * f)
      = ((n : ℚ) + 2) * PowerSeries.coeff (n + 2) f
          - ((2 * (n : ℚ)) + 3) * a * PowerSeries.coeff (n + 1) f
          + ((n : ℚ) + 1) * PowerSeries.coeff n f := by
  have hsplit : beukersQ a * (PowerSeries.derivative (R := ℚ) f) + (X - C a) * f
      = (PowerSeries.derivative (R := ℚ) f) - C (2 * a) * (X * PowerSeries.derivative (R := ℚ) f) + X ^ 2 * PowerSeries.derivative (R := ℚ) f
          + X * f - C a * f := by
    unfold beukersQ
    ring
  rw [hsplit]
  let F : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) f
  have hF : ∀ m, PowerSeries.coeff m F = PowerSeries.coeff (m + 1) f * ((m : ℚ) + 1) := by
    intro m
    exact PowerSeries.coeff_derivative f m
  have hX1 : ∀ m, PowerSeries.coeff (m + 1) (X * F) = PowerSeries.coeff m F := by
    intro m
    simpa using (PowerSeries.coeff_X_pow_mul F 1 m)
  have hX2 : ∀ m, PowerSeries.coeff (m + 2) (X ^ 2 * F) = PowerSeries.coeff m F := by
    intro m
    exact PowerSeries.coeff_X_pow_mul F 2 m
  have hXf : ∀ m, PowerSeries.coeff (m + 1) (X * f) = PowerSeries.coeff m f := by
    intro m
    simpa using (PowerSeries.coeff_X_pow_mul f 1 m)
  -- distribute the coefficient over the sum
  have hd : PowerSeries.coeff (n + 1) ((PowerSeries.derivative (R := ℚ) f) - C (2 * a) * (X * F) + X ^ 2 * F + X * f - C a * f)
      = PowerSeries.coeff (n + 1) (PowerSeries.derivative (R := ℚ) f)
          - PowerSeries.coeff (n + 1) (C (2 * a) * (X * F))
          + PowerSeries.coeff (n + 1) (X ^ 2 * F)
          + PowerSeries.coeff (n + 1) (X * f) - PowerSeries.coeff (n + 1) (C a * f) := by
    simp [F]
  rw [hd]
  -- per-term coefficient values
  have hT1 : PowerSeries.coeff (n + 1) (PowerSeries.derivative (R := ℚ) f) =
      ((n : ℚ) + 2) * PowerSeries.coeff (n + 2) f := by
    rw [PowerSeries.coeff_derivative]
    ring_nf
    rw [Nat.cast_add]
    ring
  have hT2 : PowerSeries.coeff (n + 1) (C (2 * a) * (X * F)) =
      (2 * a) * ((n : ℚ) + 1) * PowerSeries.coeff (n + 1) f := by
    rw [PowerSeries.coeff_C_mul]
    rw [hX1 n]
    rw [hF n]
    ring
  have hT3 : PowerSeries.coeff (n + 1) (X ^ 2 * F) = (n : ℚ) * PowerSeries.coeff n f := by
    cases n with
    | zero =>
        have hs : X ^ 2 * F = X * (X * F) := by rw [pow_two]; ring
        rw [hs]
        have h01 : PowerSeries.coeff 1 (X * (X * F)) = 0 := by
          simpa using (PowerSeries.coeff_X_pow_mul (X * F) 1 0)
        simpa using h01
    | succ n0 =>
        rw [show (n0 + 1) + 1 = n0 + 2 by omega]
        rw [hX2 n0]
        rw [hF n0]
        rw [show ((n0 : ℚ) + 1) = ((n0 + 1 : ℕ) : ℚ) by norm_num]
        ring
  have hT4 : PowerSeries.coeff (n + 1) (X * f) = PowerSeries.coeff n f := by
    exact hXf n
  have hT5 : PowerSeries.coeff (n + 1) (C a * f) = a * PowerSeries.coeff (n + 1) f := by
    exact PowerSeries.coeff_C_mul (n + 1) f a
  rw [hT1, hT2, hT3, hT4, hT5]
  ring


/-- a series satisfying the homogeneous ODE with zero constant term is zero -/
lemma ode_homogeneous_eq_zero_of_zero (a : ℚ) {f : PowerSeries ℚ}
    (h : beukersQ a * (PowerSeries.derivative (R := ℚ) f) + (X - C a) * f = 0)
    (hf0 : PowerSeries.coeff 0 f = 0) : f = 0 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact hf0
      | succ k =>
          cases k with
          | zero =>
              -- coefficient 1
              have hc0 := congrArg (fun s : PowerSeries ℚ => PowerSeries.coeff 0 s) h
              rw [coeff_ode_hom_zero] at hc0
              rw [hf0, mul_zero] at hc0
              simpa using hc0
          | succ k0 =>
              -- n = k0+2: use the recurrence at coefficient (k0+1)
              have hc1 := congrArg (fun s : PowerSeries ℚ => PowerSeries.coeff (k0 + 1) s) h
              rw [coeff_ode_hom_succ a f k0] at hc1
              have ih1 : PowerSeries.coeff (k0 + 1) f = 0 := ih (k0 + 1) (by omega)
              have ih0 : PowerSeries.coeff k0 f = 0 := ih k0 (by omega)
              rw [ih1, ih0, mul_zero, mul_zero, add_zero, sub_zero] at hc1
              -- hc1 : (k0+2)·f_{k0+2}·... hmm check shape: ((k0:ℚ)+2)·coeff(k0+2) f − 0 + 0 = 0
              have hnz : ((k0 : ℚ) + 2) ≠ 0 := by positivity
              have hpr : ((k0 : ℚ) + 2) * PowerSeries.coeff (k0 + 2) f = 0 := by
                -- from hc1
                simpa using hc1
              exact (mul_eq_zero.mp hpr).resolve_left hnz

/-- coefficient zero of the antiderivative -/
lemma beukersInt_coeff_zero (a : ℚ) : PowerSeries.coeff 0 (beukersInt a) = 0 := by
  unfold beukersInt
  simp

/-- the companion series equals `A·∫A`: `H = A · W` where `W′ = A`, `W(0)=0` -/
lemma beukersH_eq_A_mul_int (a : ℚ) : beukersH a = beukersA a * beukersInt a := by
  let Q : PowerSeries ℚ := beukersQ a
  let AB : PowerSeries ℚ := beukersA a * beukersInt a
  have hC : Q * (PowerSeries.derivative (R := ℚ)) AB + (X - C a) * AB = 1 := by
    dsimp [Q, C]
    exact beukersA_mul_int_ode a
  have hH : Q * (PowerSeries.derivative (R := ℚ)) (beukersH a) + (X - C a) * (beukersH a) = 1 := by
    dsimp [Q]
    simpa [beukersQ] using (beukersH_ode a)
  have hC0 : PowerSeries.coeff 0 AB = 0 := by
    dsimp [AB]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [map_mul (PowerSeries.constantCoeff (R := ℚ))]
    have hA0 : PowerSeries.constantCoeff (beukersA a) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, beukersA_coeff_zero]
    have hW0 : PowerSeries.constantCoeff (beukersInt a) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, beukersInt_coeff_zero]
    rw [hA0, hW0]
    simp
  have hH0 : PowerSeries.coeff 0 (beukersH a) = 0 := beukersH_coeff_zero a
  have hf : Q * (PowerSeries.derivative (R := ℚ)) (AB - beukersH a) + (X - C a) * (AB - beukersH a) = 0 := by
    calc
      Q * (PowerSeries.derivative (R := ℚ)) (AB - beukersH a) + (X - C a) * (AB - beukersH a)
          = (Q * (PowerSeries.derivative (R := ℚ)) AB - Q * (PowerSeries.derivative (R := ℚ)) (beukersH a))
              + ((X - C a) * AB - (X - C a) * (beukersH a)) := by
              rw [map_sub]
              ring
      _ = (Q * (PowerSeries.derivative (R := ℚ)) AB + (X - C a) * AB) - (Q * (PowerSeries.derivative (R := ℚ)) (beukersH a) + (X - C a) * (beukersH a)) := by ring
      _ = 1 - 1 := by rw [hC, hH]
      _ = 0 := by norm_num
  have hC0c : PowerSeries.constantCoeff AB = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hC0
  have hH0c : PowerSeries.constantCoeff (beukersH a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hH0
  have hf0 : PowerSeries.coeff 0 (AB - beukersH a) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [hC0c, hH0c]
  have hEq : AB - beukersH a = 0 := ode_homogeneous_eq_zero_of_zero a hf hf0
  dsimp [AB] at hEq
  exact (sub_eq_zero.mp hEq).symm

/-! ## Coefficient read-off `v_n(a) = Σ_{j=1}^{n} u_{n−j}(a)·u_{j−1}(a)/j`

From the companion identity `H = A·W` (`beukersH_eq_A_mul_int`, with
`W = ∫₀ˣ A` the formal antiderivative) we extract the coefficients of the
companion series coefficient-wise.  Since `W` has coefficients
`w_k = u_{k−1}/k` for `k ≥ 1` (and `w_0 = 0`), the product coefficient
`[x^n](A·W)` is the finite convolution `Σ_{j=1}^n u_{n−j}·u_{j−1}/j`. -/

/-- coefficient of the antiderivative `W`: `w_0 = 0`, `w_k = u_{k−1}/k` for `k ≥ 1` -/
lemma beukersInt_coeff (a : ℚ) (m : ℕ) :
    PowerSeries.coeff m (beukersInt a) = if m = 0 then 0 else beukersU a (m - 1) / (m : ℚ) := by
  unfold beukersInt
  rw [PowerSeries.coeff_mk]

/-- the `[x^n](A·W)` convolution, reduced to the range sum over the companion
coefficients `w_k = u_{k−1}/k` — pure cast denominators (auxiliary for
`beukersV_eq_sum`) -/
lemma beukersV_eq_sum_aux (a : ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (beukersA a) * PowerSeries.coeff (n - k) (beukersInt a))
      = ∑ j ∈ Finset.Icc 1 n, beukersU a (n - j) * (beukersU a (j - 1) / (j : ℚ)) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (beukersA a) * PowerSeries.coeff (n - k) (beukersInt a))
        = ∑ k ∈ Finset.range (n + 1),
            beukersU a k * (if n - k = 0 then 0 else beukersU a (n - k - 1) / ((n - k : ℕ) : ℚ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [beukersA_coeff, beukersInt_coeff]
    _ = ∑ k ∈ Finset.range n, beukersU a k * (beukersU a (n - k - 1) / ((n - k : ℕ) : ℚ)) := by
            -- drop the k = n term, whose coefficient w_0 = 0
            rw [Finset.sum_range_succ]
            have hfn : (if n - n = 0 then (0 : ℚ) else beukersU a (n - n - 1) / ((n - n : ℕ) : ℚ)) = 0 := by
              rw [Nat.sub_self]
              simp
            rw [hfn]
            simp
            apply Finset.sum_congr rfl
            intro k hk
            have hnk : n - k ≠ 0 := by
              have hk' : k < n := Finset.mem_range.mp hk
              omega
            rw [if_neg hnk]
    _ = ∑ j ∈ Finset.Icc 1 n, beukersU a (n - j) * (beukersU a (j - 1) / (j : ℚ)) := by
            -- reindex k ↦ j = n − k: {k < n} ↔ {1 ≤ j ≤ n}
            refine Finset.sum_bij (fun k hk => n - k) ?_ ?_ ?_ ?_
            · intro k hk
              have hk' : k < n := Finset.mem_range.mp hk
              simp [Finset.mem_Icc]
              omega
            · intro k₁ hk₁ k₂ hk₂ h
              have hk₁' : k₁ < n := Finset.mem_range.mp hk₁
              have hk₂' : k₂ < n := Finset.mem_range.mp hk₂
              omega
            · intro j hj
              have hj₁ : 1 ≤ j := (Finset.mem_Icc.mp hj).1
              have hj₂ : j ≤ n := (Finset.mem_Icc.mp hj).2
              refine ⟨n - j, Finset.mem_range.mpr (by omega), ?_⟩
              omega
            · intro k hk
              have hk' : k < n := Finset.mem_range.mp hk
              have h₁ : n - (n - k) = k := by omega
              rw [h₁]

/-- `v_n(a) = Σ_{j=1}^{n} u_{n−j}(a)·u_{j−1}(a)/j` — the companion
coefficient read-off from `H = A·W`. -/
lemma beukersV_eq_sum (a : ℚ) (n : ℕ) :
    beukersV a n = ∑ j ∈ Finset.Icc 1 n, beukersU a (n - j) * (beukersU a (j - 1) / (j : ℚ)) := by
  calc
    beukersV a n = PowerSeries.coeff n (beukersA a * beukersInt a) := by
        rw [← beukersH_coeff, beukersH_eq_A_mul_int]
    _ = ∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff k (beukersA a) * PowerSeries.coeff (n - k) (beukersInt a) := by
        rw [PowerSeries.coeff_mul]
        exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (beukersA a) * PowerSeries.coeff j (beukersInt a)) n
    _ = ∑ j ∈ Finset.Icc 1 n, beukersU a (n - j) * (beukersU a (j - 1) / (j : ℚ)) := by
        exact beukersV_eq_sum_aux a n


/-! ## The denominator claim: `[1,…,n]·v_n(a) ∈ ℤ` for odd `a`

From the read-off `v_n = Σ_{j=1}^n u_{n−j}·u_{j−1}/j` and the integrality
`u_k(a) ∈ ℤ` for odd `a`, each summand, multiplied by the lcm
`L = [1,…,n]` of `{1,…,n}`, becomes `(L/j)·u_{n−j}·u_{j−1}`, a product of
integers (because `j ∣ L`).  Hence `L·v_n(a) ∈ ℤ`: this is the
"denominator half" of the paper's claim that
`H(a,x) = Σ v_n(a) x^n` has `[1,…,n]·v_n(a) ∈ ℤ` for odd `a`. -/

lemma beukersV_lcm_term_int (z : ℤ) (hz : Odd z) (n j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
    ∃ t : ℤ, (t : ℚ) = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ)
        * (beukersU (z : ℚ) (n - j) * (beukersU (z : ℚ) (j - 1) / (j : ℚ))) := by
  let L : ℕ := (Finset.Icc 1 n).lcm id
  have hjL0 : j ∣ ((Finset.Icc 1 n).lcm (fun x : ℕ => x)) := by
    exact Finset.dvd_lcm (s := (Finset.Icc 1 n)) (f := fun x : ℕ => x) hj
  have hjL : j ∣ L := by
    exact hjL0
  have hj0 : j ≠ 0 := by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    omega
  obtain ⟨tA, hA⟩ := beukersU_int_of_odd z hz (n - j)
  obtain ⟨tB, hB⟩ := beukersU_int_of_odd z hz (j - 1)
  refine ⟨(((L / j : ℕ) : ℤ) * tA * tB), ?_⟩
  calc
    (↑((((L / j : ℕ) : ℤ) * tA * tB) : ℤ) : ℚ)
        = (((L / j : ℕ) : ℚ)) * (tA : ℚ) * (tB : ℚ) := by
            simp only [Int.cast_mul, Int.cast_natCast]
    _ = (((L / j : ℕ) : ℚ)) * beukersU (z : ℚ) (n - j) * beukersU (z : ℚ) (j - 1) := by
            rw [hA, hB]
    _ = ((L : ℚ) / (j : ℚ)) * beukersU (z : ℚ) (n - j) * beukersU (z : ℚ) (j - 1) := by
            rw [Nat.cast_div (K := ℚ) hjL (by exact_mod_cast hj0)]
    _ = (L : ℚ) * (beukersU (z : ℚ) (n - j) * (beukersU (z : ℚ) (j - 1) / (j : ℚ))) := by
            ring
    _ = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ)
            * (beukersU (z : ℚ) (n - j) * (beukersU (z : ℚ) (j - 1) / (j : ℚ))) := by
            rfl

lemma beukersV_lcm_int_of_odd (z : ℤ) (hz : Odd z) (n : ℕ) :
    ∃ t : ℤ, (t : ℚ) = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) * beukersV (z : ℚ) n := by
  let L : ℕ := (Finset.Icc 1 n).lcm id
  let tA : ℕ → ℤ := fun j => Classical.choose (beukersU_int_of_odd z hz (n - j))
  let tB : ℕ → ℤ := fun j => Classical.choose (beukersU_int_of_odd z hz (j - 1))
  have hA : ∀ j, (tA j : ℚ) = beukersU (z : ℚ) (n - j) := by
    intro j
    exact Classical.choose_spec (beukersU_int_of_odd z hz (n - j))
  have hB : ∀ j, (tB j : ℚ) = beukersU (z : ℚ) (j - 1) := by
    intro j
    exact Classical.choose_spec (beukersU_int_of_odd z hz (j - 1))
  refine ⟨∑ j ∈ Finset.Icc 1 n, (((L / j : ℕ) : ℤ) * tA j * tB j), ?_⟩
  calc
    (↑(∑ j ∈ Finset.Icc 1 n, (((L / j : ℕ) : ℤ) * tA j * tB j)) : ℚ)
        = ∑ j ∈ Finset.Icc 1 n, ((((L / j : ℕ) : ℚ)) * (tA j : ℚ) * (tB j : ℚ)) := by
            rw [Int.cast_sum]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Int.cast_mul, Int.cast_natCast]
    _ = ∑ j ∈ Finset.Icc 1 n, ((((L / j : ℕ) : ℚ)) * beukersU (z : ℚ) (n - j) * beukersU (z : ℚ) (j - 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hA j, hB j]
    _ = ∑ j ∈ Finset.Icc 1 n, ((L : ℚ) * (beukersU (z : ℚ) (n - j) * (beukersU (z : ℚ) (j - 1) / (j : ℚ)))) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjL0 : j ∣ ((Finset.Icc 1 n).lcm (fun x : ℕ => x)) := by
              exact Finset.dvd_lcm (s := (Finset.Icc 1 n)) (f := fun x : ℕ => x) hj
            have hjL : j ∣ L := by
              exact hjL0
            have hj0 : j ≠ 0 := by
              have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
              omega
            rw [Nat.cast_div (K := ℚ) hjL (by exact_mod_cast hj0)]
            ring
    _ = (L : ℚ) * ∑ j ∈ Finset.Icc 1 n, (beukersU (z : ℚ) (n - j) * (beukersU (z : ℚ) (j - 1) / (j : ℚ))) := by
            rw [← Finset.mul_sum]
    _ = (L : ℚ) * beukersV (z : ℚ) n := by
            rw [beukersV_eq_sum]

/-! ## Assembly: the coefficient arithmetic of eq. (beukersB)

For odd `a` the paper records (eq. (beukersB)): `A(a,x) = Σ u_n x^n ∈ ℤ[[x]]`
and `[1,2,…,n]·v_n(a) ∈ ℤ` for the companion coefficients.  Both halves are
now proved: `beukersU_int_of_odd` and `beukersV_lcm_int_of_odd`.  We record
the joint statement here. -/

/-- **Coefficient arithmetic of the Beukers pair** (paper eq. (beukersB)):
for odd integer `a`, `u_n(a) ∈ ℤ` and `[1,…,n]·v_n(a) ∈ ℤ` for every `n`. -/
lemma beukers_coeff_arithmetic (z : ℤ) (hz : Odd z) (n : ℕ) :
    (∃ tu : ℤ, (tu : ℚ) = beukersU (z : ℚ) n)
      ∧ ∃ tv : ℤ, (tv : ℚ) = (((Finset.Icc 1 n).lcm id : ℕ) : ℚ) * beukersV (z : ℚ) n := by
  exact ⟨beukersU_int_of_odd z hz n, beukersV_lcm_int_of_odd z hz n⟩

/-! ## The real analytic companion: `η_a`, `ρ_a`, and the closed-form identity

This section begins the **analytic chapter** of the Apéry-limit brick
(`lim_n v_n/u_n = ½·log((a+1)/(a−1))`, paper eq. (beukerslimit)).  The
real functions here are the analytic incarnations of the formal series of
the module:

* `A(a,x) = 1/√(1 − 2a·x + x²)` — the real Beukers function (the analytic
  meaning of `Σ u_n x^n`), with singularities at `x = ρ_a` and
  `x = 1/ρ_a`, `ρ_a := a − √(a²−1)` (the smaller root of
  `Q = 1 − 2a·x + x²`);
* `W(a,x) = log((a+1)/(a−x+√Q))` — the closed-form antiderivative of
  `A` with `W(0) = 0` (`beukersWReal_zero`, `beukersWReal_hasDerivAt`,
  `beukersWReal_eq_integral` = the FTC `W(x) = ∫₀ˣ A`);
* the **boundary value** `W(a,ρ_a) = η_a := ½·log((a+1)/(a−1))`
  (`beukersWReal_rho_eq_eta`) — the arithmetic anchor tying the companion
  series to the logarithm, since the companion function
  `H(a,x) = A(a,x)·W(a,x)` satisfies the paper's functional identity
  (eq. (beukersB)) `H(a,x) − η_a·A(a,x) = A(a,x)·(W(a,x) − W(a,ρ_a))`
  (`beukers_apéry_closed_form`), whose right side is
  `A(a,x)·∫_{ρ_a}^x dt/√(1−2at+t²)` in the FTC sense.

All statements are for real `a ≥ 3` (the paper uses odd integers `a = 1+2m`).
-/

def beukersRho (a : ℝ) : ℝ := a - Real.sqrt (a ^ 2 - 1)
def beukersQuad (a x : ℝ) : ℝ := 1 - 2 * a * x + x ^ 2
def beukersSqrtQ (a x : ℝ) : ℝ := Real.sqrt (beukersQuad a x)
def beukersAReal (a x : ℝ) : ℝ := (beukersSqrtQ a x)⁻¹
def beukersWReal (a x : ℝ) : ℝ :=
  Real.log ((a + 1) / (a - x + beukersSqrtQ a x))
def beukersEta (a : ℝ) : ℝ := (1 / 2) * Real.log ((a + 1) / (a - 1))

lemma beukers_sq_sub_one_nonneg (a : ℝ) (ha : 3 ≤ a) : 0 ≤ a ^ 2 - 1 := by
  have h9 : (3 : ℝ) ^ 2 ≤ a ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num : 0 ≤ (3 : ℝ)) ha 2
  nlinarith

lemma beukers_rho_sq_identity (a : ℝ) (ha : 3 ≤ a) :
    (Real.sqrt (a ^ 2 - 1)) ^ 2 = a ^ 2 - 1 := by
  exact Real.sq_sqrt (beukers_sq_sub_one_nonneg a ha)

lemma beukers_sqrt_sq_sub_one_pos (a : ℝ) (ha : 3 ≤ a) : 0 < Real.sqrt (a ^ 2 - 1) := by
  apply Real.sqrt_pos.2
  have h8 : (8 : ℝ) ≤ a ^ 2 - 1 := by
    have h9 : (3 : ℝ) ^ 2 ≤ a ^ 2 := by
      exact pow_le_pow_left₀ (by norm_num : 0 ≤ (3 : ℝ)) ha 2
    nlinarith
  linarith

lemma beukers_rho_lt_a (a : ℝ) (ha : 3 ≤ a) : beukersRho a < a := by
  dsimp [beukersRho]
  have hsq : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
  linarith

lemma beukers_rho_pos (a : ℝ) (ha : 3 ≤ a) : 0 < beukersRho a := by
  have hsq : Real.sqrt (a ^ 2 - 1) < a := by
    have h1 : a ^ 2 - 1 < a ^ 2 := by nlinarith
    have hle : Real.sqrt (a ^ 2 - 1) ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_sq_eq_abs] at hle
    have ha0 : 0 ≤ a := by linarith
    rw [abs_of_nonneg ha0] at hle
    have hne : Real.sqrt (a ^ 2 - 1) ≠ a := by
      intro hEq
      have hEq2 : (Real.sqrt (a ^ 2 - 1)) ^ 2 = a ^ 2 := by rw [hEq]
      rw [beukers_rho_sq_identity a ha] at hEq2
      nlinarith
    exact lt_of_le_of_ne hle hne
  dsimp [beukersRho]
  linarith

lemma beukersQuad_rho_zero (a : ℝ) (ha : 3 ≤ a) : beukersQuad a (beukersRho a) = 0 := by
  let s : ℝ := Real.sqrt (a ^ 2 - 1)
  have hs : s ^ 2 = a ^ 2 - 1 := by
    dsimp [s]
    exact beukers_rho_sq_identity a ha
  have hstep : 1 - 2 * a * (a - s) + (a - s) ^ 2 = s ^ 2 - a ^ 2 + 1 := by ring
  dsimp [beukersQuad, beukersRho, s]
  rw [hstep]
  rw [hs]
  ring

lemma beukersQuad_factor (a x : ℝ) (ha : 3 ≤ a) :
    beukersQuad a x = (x - beukersRho a) * (x - (a + Real.sqrt (a ^ 2 - 1))) := by
  let s : ℝ := Real.sqrt (a ^ 2 - 1)
  have hs : s ^ 2 = a ^ 2 - 1 := by
    dsimp [s]
    exact beukers_rho_sq_identity a ha
  have hring : (x - (a - s)) * (x - (a + s)) = x ^ 2 - 2 * a * x + (a ^ 2 - s ^ 2) := by ring
  dsimp [beukersQuad, beukersRho, s]
  rw [hring]
  rw [hs]
  ring

lemma beukersQuad_pos_of_lt_rho (a x : ℝ) (ha : 3 ≤ a) (hx : x < beukersRho a) :
    0 < beukersQuad a x := by
  let r : ℝ := a + Real.sqrt (a ^ 2 - 1)
  have hfac : beukersQuad a x = (x - beukersRho a) * (x - r) := by
    dsimp [r]
    exact beukersQuad_factor a x ha
  rw [hfac]
  apply mul_pos_of_neg_of_neg
  · linarith
  · have hr : beukersRho a < r := by
      dsimp [r, beukersRho]
      have hsq : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
      linarith
    linarith

lemma beukers_denom_pos_of_lt_rho (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hx : x < beukersRho a) :
    0 < a - x + Real.sqrt (beukersQuad a x) := by
  have hx_lt_a : x < a := lt_trans hx (beukers_rho_lt_a a ha)
  have hsq : 0 ≤ Real.sqrt (beukersQuad a x) := Real.sqrt_nonneg _
  linarith

-- ============ derivative chain ============

lemma beukers_quad_hasDerivAt_sq (a x : ℝ) :
    HasDerivAt (fun t : ℝ => (a - t) ^ 2 - (a ^ 2 - 1)) (2 * (a - x) * -1 - 0) x := by
  have h_am : HasDerivAt (fun t : ℝ => a - t) (-1) x :=
    HasDerivAt.const_sub a (hasDerivAt_id x)
  have h_sq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * (a - x)) (a - x) := by
    simpa using (hasDerivAt_pow 2 (a - x))
  have hcomp : HasDerivAt (fun t : ℝ => (a - t) ^ 2) (2 * (a - x) * -1) x :=
    h_sq.comp x h_am
  have hconst : HasDerivAt (fun t : ℝ => (a ^ 2 - 1 : ℝ)) 0 x :=
    hasDerivAt_const x (a ^ 2 - 1)
  exact hcomp.sub hconst

lemma beukersQuad_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun t : ℝ => beukersQuad a t) (2 * x - 2 * a) x := by
  have h := beukers_quad_hasDerivAt_sq a x
  have hpoint : (fun t : ℝ => beukersQuad a t) = fun t => (a - t) ^ 2 - (a ^ 2 - 1) := by
    funext t
    dsimp [beukersQuad]
    ring
  rw [hpoint]
  have hval : 2 * x - 2 * a = 2 * (a - x) * -1 - 0 := by ring
  rwa [hval]

lemma beukers_sqrtQ_raw_hasDerivAt (a x : ℝ) (hQne : beukersQuad a x ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (beukersQuad a t))
      ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a)) x := by
  exact (Real.hasDerivAt_sqrt hQne).comp x (beukersQuad_hasDerivAt a x)

lemma beukers_denom_raw_hasDerivAt (a x : ℝ) (hQne : beukersQuad a x ≠ 0) :
    HasDerivAt (fun t : ℝ => a - t + Real.sqrt (beukersQuad a t))
      (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a))) x := by
  have h_am : HasDerivAt (fun t : ℝ => a - t) (-1) x :=
    HasDerivAt.const_sub a (hasDerivAt_id x)
  exact h_am.add (beukers_sqrtQ_raw_hasDerivAt a x hQne)

lemma beukers_log_denom_raw_hasDerivAt (a x : ℝ) (hQne : beukersQuad a x ≠ 0)
    (hUx : a - x + Real.sqrt (beukersQuad a x) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (a - t + Real.sqrt (beukersQuad a t)))
      ((a - x + Real.sqrt (beukersQuad a x))⁻¹ *
        (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a)))) x := by
  exact (Real.hasDerivAt_log hUx).comp x (beukers_denom_raw_hasDerivAt a x hQne)

lemma beukersWReal_hasDerivAt (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    HasDerivAt (beukersWReal a) (beukersAReal a x) x := by
  change HasDerivAt (fun t : ℝ => Real.log ((a + 1) / (a - t + Real.sqrt (beukersQuad a t))))
      ((Real.sqrt (beukersQuad a x))⁻¹) x
  have hQpos : 0 < beukersQuad a x := beukersQuad_pos_of_lt_rho a x ha hxρ
  have hQne : beukersQuad a x ≠ 0 := ne_of_gt hQpos
  have hUx_pos : 0 < a - x + Real.sqrt (beukersQuad a x) := beukers_denom_pos_of_lt_rho a ha hxρ
  have hUx_ne : a - x + Real.sqrt (beukersQuad a x) ≠ 0 := ne_of_gt hUx_pos
  have hlogU : HasDerivAt (fun t : ℝ => Real.log (a - t + Real.sqrt (beukersQuad a t)))
      ((a - x + Real.sqrt (beukersQuad a x))⁻¹ *
        (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a)))) x :=
    beukers_log_denom_raw_hasDerivAt a x hQne hUx_ne
  have h_minus : HasDerivAt
      ((fun _ : ℝ => Real.log (a + 1)) - (fun t : ℝ => Real.log (a - t + Real.sqrt (beukersQuad a t))))
      (0 - ((a - x + Real.sqrt (beukersQuad a x))⁻¹ *
        (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a))))) x := by
    exact (hasDerivAt_const x (Real.log (a + 1))).sub hlogU
  have hloc : (fun t : ℝ => Real.log ((a + 1) / (a - t + Real.sqrt (beukersQuad a t))))
      =ᶠ[𝓝 x] ((fun _ : ℝ => Real.log (a + 1)) - (fun t : ℝ => Real.log (a - t + Real.sqrt (beukersQuad a t)))) := by
    have hUcont : ContinuousAt (fun t : ℝ => a - t + Real.sqrt (beukersQuad a t)) x :=
      (beukers_denom_raw_hasDerivAt a x hQne).continuousAt
    have hUev : ∀ᶠ t in 𝓝 x, a - t + Real.sqrt (beukersQuad a t) ≠ 0 :=
      hUcont.eventually_ne hUx_ne
    have h_a1 : (a : ℝ) + 1 ≠ 0 := by
      have : 0 < (a : ℝ) + 1 := by linarith
      exact ne_of_gt this
    filter_upwards [hUev] with t ht
    exact Real.log_div h_a1 ht
  have hfin : HasDerivAt (fun t : ℝ => Real.log ((a + 1) / (a - t + Real.sqrt (beukersQuad a t))))
      (0 - ((a - x + Real.sqrt (beukersQuad a x))⁻¹ *
        (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a))))) x :=
    h_minus.congr_of_eventuallyEq hloc
  have hval : 0 - ((a - x + Real.sqrt (beukersQuad a x))⁻¹ *
        (-1 + ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a))))
      = (Real.sqrt (beukersQuad a x))⁻¹ := by
    have hsne : Real.sqrt (beukersQuad a x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hQpos)
    field_simp [hsne, hUx_ne]
    ring
  rw [← hval]
  exact hfin



-- ============ boundary values and the FTC ============

lemma beukersWReal_zero (a : ℝ) : beukersWReal a 0 = 0 := by
  dsimp [beukersWReal, beukersSqrtQ, beukersQuad]
  norm_num [Real.sqrt_one]

lemma beukersWReal_rho_eq_eta (a : ℝ) (ha : 3 ≤ a) :
    beukersWReal a (beukersRho a) = beukersEta a := by
  let s : ℝ := Real.sqrt (a ^ 2 - 1)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact beukers_sqrt_sq_sub_one_pos a ha
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hsqrt : s = Real.sqrt ((a + 1) * (a - 1)) := by
    dsimp [s]
    congr 1
    ring
  have hsqrtQ_rho : beukersSqrtQ a (beukersRho a) = 0 := by
    dsimp [beukersSqrtQ]
    rw [beukersQuad_rho_zero a ha]
    simp
  have hW : beukersWReal a (beukersRho a) = Real.log ((a + 1) / s) := by
    dsimp [beukersWReal, s]
    rw [hsqrtQ_rho]
    dsimp [beukersRho]
    ring_nf
  calc
    beukersWReal a (beukersRho a) = Real.log ((a + 1) / s) := hW
    _ = (1 / 2) * Real.log ((a + 1) / (a - 1)) := by
        have h1' : 0 < (a : ℝ) + 1 := by linarith
        have h1 : (a : ℝ) + 1 ≠ 0 := ne_of_gt h1'
        have h2' : 0 < (a : ℝ) - 1 := by linarith
        have h2 : (a : ℝ) - 1 ≠ 0 := ne_of_gt h2'
        have harg : 0 ≤ (a + 1) * (a - 1) := by
          exact mul_nonneg (le_of_lt h1') (le_of_lt h2')
        have hlog_s : Real.log s = (1 / 2) * Real.log ((a + 1) * (a - 1)) := by
          calc
            Real.log s = Real.log (Real.sqrt ((a + 1) * (a - 1))) := by rw [hsqrt]
            _ = Real.log ((a + 1) * (a - 1)) / 2 := Real.log_sqrt harg
            _ = (1 / 2) * Real.log ((a + 1) * (a - 1)) := by ring
        calc
          Real.log ((a + 1) / s) = Real.log (a + 1) - Real.log s := Real.log_div h1 hs_ne
          _ = Real.log (a + 1) - (1 / 2) * Real.log ((a + 1) * (a - 1)) := by rw [hlog_s]
          _ = Real.log (a + 1) - (1 / 2) * (Real.log (a + 1) + Real.log (a - 1)) := by
              rw [Real.log_mul h1 h2]
          _ = (1 / 2) * (Real.log (a + 1) - Real.log (a - 1)) := by ring
          _ = (1 / 2) * Real.log ((a + 1) / (a - 1)) := by
              rw [← Real.log_div h1 h2]
    _ = beukersEta a := by
        rfl

-- A(x) = (√Q(x))⁻¹ is continuous on [0, x] for x < ρ
lemma beukersAReal_continuousOn_Icc (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    ContinuousOn (fun t : ℝ => beukersAReal a t) (Set.uIcc 0 x) := by
  have hcont_sqrt : ContinuousOn (fun t : ℝ => Real.sqrt (beukersQuad a t)) (Set.uIcc 0 x) := by
    have hquad : Continuous fun t : ℝ => beukersQuad a t := by
      dsimp [beukersQuad]
      fun_prop
    exact hquad.continuousOn.sqrt
  have hsq_ne : ∀ t ∈ Set.uIcc 0 x, Real.sqrt (beukersQuad a t) ≠ 0 := by
    intro t ht
    have htρ : t < beukersRho a := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact lt_of_le_of_lt h.2 hxρ
      · exact lt_of_le_of_lt h.2 (beukers_rho_pos a ha)
    have hQpos : 0 < beukersQuad a t := beukersQuad_pos_of_lt_rho a t ha htρ
    exact ne_of_gt (Real.sqrt_pos.2 hQpos)
  have hcont_inv : ContinuousOn (fun t : ℝ => (Real.sqrt (beukersQuad a t))⁻¹) (Set.uIcc 0 x) :=
    ContinuousOn.inv₀ hcont_sqrt hsq_ne
  simpa [beukersAReal, beukersSqrtQ] using hcont_inv

/-- **FTC**: for `0 ≤ x < ρ`, `W(x) = ∫₀ˣ A(t) dt` — the antiderivative
relation making `W` (and hence `H = A·W`) the integral companion of `A`. -/
lemma beukersWReal_eq_integral (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hx0 : 0 ≤ x) (hxρ : x < beukersRho a) :
    (∫ t in 0..x, beukersAReal a t) = beukersWReal a x := by
  have hderiv : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (beukersWReal a) (beukersAReal a t) t := by
    intro t ht
    have htρ : t < beukersRho a := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact lt_of_le_of_lt h.2 hxρ
      · exact lt_of_le_of_lt h.2 (beukers_rho_pos a ha)
    exact beukersWReal_hasDerivAt a ha htρ
  have hint : IntervalIntegrable (fun t : ℝ => beukersAReal a t) MeasureTheory.volume 0 x :=
    ContinuousOn.intervalIntegrable (beukersAReal_continuousOn_Icc a ha hxρ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := beukersWReal a)
    (f' := fun t : ℝ => beukersAReal a t) hderiv hint
  -- hFTC : ∫ t in 0..x, beukersAReal a t = beukersWReal a x - beukersWReal a 0
  rw [beukersWReal_zero a] at hFTC
  simpa using hFTC

/-- the closed-form functional identity behind the paper's eq. (beukersB):
`H − ηA = A·(W − W(ρ))` with `W(ρ) = η` (`beukersWReal_rho_eq_eta`) and
`W(x) − W(ρ) = ∫_ρ^x A` in the FTC sense (`beukersWReal_eq_integral` +
continuity), where `H(a,x) := A(a,x)·W(a,x)` is the companion function. -/
lemma beukers_apéry_closed_form (a : ℝ) (ha : 3 ≤ a) (x : ℝ) :
    beukersAReal a x * (beukersWReal a x - beukersEta a)
      = beukersAReal a x * (beukersWReal a x - beukersWReal a (beukersRho a)) := by
  rw [beukersWReal_rho_eq_eta a ha]

/-! ## The complex quadratic `Q(z) = (1 − ρz)(1 − rz)` and the square-root coordinate

This section opens the **complex-analysis chapter** of the Apéry-limit brick:
the analytic continuation through the square-root singularity at `ρ`.

Objects: the complexified quadratic `beukersQuadC a z = 1 − 2a·z + z²` and
its roots `ρ = beukersRhoC a` (the Beukers singularity, `0 < ρ < 1`) and
`r = beukersRc a = a + √(a²−1) = 1/ρ` (the other root).

First coordinates committed here:

* the two factorizations `Q(z) = (1−ρz)(1−rz) = (z−ρ)(z−r)`
  (`beukersQuadC_factor_unit`, `beukersQuadC_factor`), hence the roots
  `beukersQuadC_eq_zero_iff : Q(z) = 0 ↔ z = ρ ∨ z = r`;
* `beukersQuadC_ne_zero_of_norm_lt` — `Q ≠ 0` on the open disc `|z| < ρ`
  (the region where the power series `Σ u_n z^n` is to be identified with
  `A(z) = 1/√Q(z)`);
* the derivative `beukersQuadC_hasDerivAt : Q′ = 2z − 2a` and the **simple
  root** at `ρ`: `beukersQuadC_deriv_rho_ne_zero` (`Q′(ρ) = −2√(a²−1) ≠ 0`),
  and continuity `beukersQuadC_continuous`;
* **the square-root coordinate at ρ**: under the pullback
  `z = ρ − u²` (`beukersQuadC_rho_sub_sq`),
  `Q(ρ − u²) = u²·(2c + u²)`, `c = √(a²−1)` — the quadratic becomes a
  manifest square `(u·√(2c+u²))²` with the second factor holomorphic and
  nonzero for small `u` (`beukers_rho_pull_factor_ne_zero`), which is the
  seed of the local branch of `√Q` (and hence of `A = 1/√Q`) across `ρ`.
-/


/-- ρ = a − √(a²−1) as a complex number -/
noncomputable def beukersRhoC (a : ℝ) : ℂ := (beukersRho a : ℂ)

/-- r = a + √(a²−1) = 1/ρ : the larger root of the quadratic -/
noncomputable def beukersRc (a : ℝ) : ℂ := (a + Real.sqrt (a ^ 2 - 1) : ℂ)

/-- Q(z) = 1 − 2a·z + z² over ℂ -/
def beukersQuadC (a : ℝ) (z : ℂ) : ℂ := 1 - 2 * (a : ℂ) * z + z ^ 2

lemma beukersRhoC_eq (a : ℝ) : beukersRhoC a = (a : ℂ) - (Real.sqrt (a ^ 2 - 1) : ℂ) := by
  dsimp [beukersRhoC, beukersRho]
  rw [Complex.ofReal_sub]

lemma beukersRc_eq (a : ℝ) : beukersRc a = (a : ℂ) + (Real.sqrt (a ^ 2 - 1) : ℂ) := by
  rfl

lemma beukersSqrt_sq_cast (a : ℝ) (ha : 3 ≤ a) :
    ((Real.sqrt (a ^ 2 - 1) : ℂ) ^ 2) = ((a : ℂ) ^ 2 - 1) := by
  have hs : (Real.sqrt (a ^ 2 - 1)) ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (beukers_sq_sub_one_nonneg a ha)
  calc
    ((Real.sqrt (a ^ 2 - 1) : ℂ) ^ 2) = ((Real.sqrt (a ^ 2 - 1) ^ 2 : ℝ) : ℂ) := by rw [← Complex.ofReal_pow]
    _ = ((a ^ 2 - 1 : ℝ) : ℂ) := by rw [hs]
    _ = ((a : ℂ) ^ 2 - 1) := by
        rw [Complex.ofReal_sub, Complex.ofReal_pow]
        simp

lemma beukersRhoC_norm (a : ℝ) (ha : 3 ≤ a) : ‖beukersRhoC a‖ = beukersRho a := by
  dsimp [beukersRhoC]
  have hx : ‖(((beukersRho a : ℝ) : ℂ))‖ = |beukersRho a| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx, abs_of_nonneg (le_of_lt (beukers_rho_pos a ha))]

lemma beukersRc_norm (a : ℝ) (ha : 3 ≤ a) :
    ‖beukersRc a‖ = a + Real.sqrt (a ^ 2 - 1) := by
  have hnonneg : 0 ≤ a + Real.sqrt (a ^ 2 - 1) := by
    have hsq : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  dsimp [beukersRc]
  rw [← Complex.ofReal_add]
  have hx : ‖(((a + Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))‖ = |a + Real.sqrt (a ^ 2 - 1)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx, abs_of_nonneg hnonneg]

lemma beukers_rho_lt_rc (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a < a + Real.sqrt (a ^ 2 - 1) := by
  dsimp [beukersRho]
  have hsq : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
  linarith

-- Q(z) = (1 − ρz)(1 − rz)
lemma beukersQuadC_factor_unit (a : ℝ) (ha : 3 ≤ a) (z : ℂ) :
    beukersQuadC a z = (1 - beukersRhoC a * z) * (1 - beukersRc a * z) := by
  let A : ℂ := (a : ℂ)
  let S : ℂ := (Real.sqrt (a ^ 2 - 1) : ℂ)
  have hSS : S ^ 2 = A ^ 2 - 1 := by
    dsimp [A, S]
    exact beukersSqrt_sq_cast a ha
  calc
    beukersQuadC a z = (1 - (A - S) * z) * (1 - (A + S) * z) := by
        dsimp [beukersQuadC, A]
        ring_nf
        rw [hSS]
        ring
    _ = (1 - beukersRhoC a * z) * (1 - beukersRc a * z) := by
        have hρ : beukersRhoC a = A - S := by dsimp [A, S]; exact beukersRhoC_eq a
        have hr : beukersRc a = A + S := by dsimp [A, S]; exact beukersRc_eq a
        rw [hρ, hr]

-- Q(z) = (z − ρ)(z − r)
lemma beukersQuadC_factor (a : ℝ) (ha : 3 ≤ a) (z : ℂ) :
    beukersQuadC a z = (z - beukersRhoC a) * (z - beukersRc a) := by
  let A : ℂ := (a : ℂ)
  let S : ℂ := (Real.sqrt (a ^ 2 - 1) : ℂ)
  have hSS : S ^ 2 = A ^ 2 - 1 := by
    dsimp [A, S]
    exact beukersSqrt_sq_cast a ha
  calc
    beukersQuadC a z = (z - (A - S)) * (z - (A + S)) := by
        dsimp [beukersQuadC, A]
        ring_nf
        rw [hSS]
        ring
    _ = (z - beukersRhoC a) * (z - beukersRc a) := by
        have hρ : beukersRhoC a = A - S := by dsimp [A, S]; exact beukersRhoC_eq a
        have hr : beukersRc a = A + S := by dsimp [A, S]; exact beukersRc_eq a
        rw [hρ, hr]

lemma beukersQuadC_eq_zero_iff (a : ℝ) (ha : 3 ≤ a) (z : ℂ) :
    beukersQuadC a z = 0 ↔ z = beukersRhoC a ∨ z = beukersRc a := by
  rw [beukersQuadC_factor a ha z, mul_eq_zero]
  exact or_congr sub_eq_zero sub_eq_zero

-- Q ≠ 0 on the open disc |z| < ρ
lemma beukersQuadC_ne_zero_of_norm_lt (a : ℝ) (ha : 3 ≤ a) {z : ℂ}
    (hz : ‖z‖ < ‖beukersRhoC a‖) : beukersQuadC a z ≠ 0 := by
  intro hz0
  rcases (beukersQuadC_eq_zero_iff a ha z).mp hz0 with h | h
  · have : ‖z‖ = ‖beukersRhoC a‖ := by rw [h]
    nlinarith
  · have hzr : ‖z‖ = ‖beukersRc a‖ := by rw [h]
    have hr : ‖beukersRc a‖ > ‖beukersRhoC a‖ := by
      rw [beukersRc_norm a ha, beukersRhoC_norm a ha]
      exact beukers_rho_lt_rc a ha
    nlinarith

-- derivative: Q' = 2z − 2a
lemma beukersQuadC_hasDerivAt (a : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => beukersQuadC a w) (2 * z - 2 * (a : ℂ)) z := by
  have h_am : HasDerivAt (fun w : ℂ => (a : ℂ) - w) (-1) z :=
    HasDerivAt.const_sub (a : ℂ) (hasDerivAt_id z)
  have h_sq : HasDerivAt (fun y : ℂ => y ^ 2) (2 * ((a : ℂ) - z)) ((a : ℂ) - z) := by
    simpa using (hasDerivAt_pow 2 ((a : ℂ) - z))
  have hcomp : HasDerivAt (fun w : ℂ => ((a : ℂ) - w) ^ 2) (2 * ((a : ℂ) - z) * -1) z :=
    h_sq.comp z h_am
  have hconst : HasDerivAt (fun w : ℂ => ((a : ℂ) ^ 2 - 1 : ℂ)) 0 z :=
    hasDerivAt_const z ((a : ℂ) ^ 2 - 1)
  have hsub : HasDerivAt (fun w : ℂ => ((a : ℂ) - w) ^ 2 - ((a : ℂ) ^ 2 - 1))
      (2 * ((a : ℂ) - z) * -1 - 0) z := hcomp.sub hconst
  have hpoint : (fun w : ℂ => beukersQuadC a w) = fun w : ℂ => ((a : ℂ) - w) ^ 2 - ((a : ℂ) ^ 2 - 1) := by
    funext w
    dsimp [beukersQuadC]
    ring
  rw [hpoint]
  have hval : 2 * z - 2 * (a : ℂ) = 2 * ((a : ℂ) - z) * -1 - 0 := by ring
  rwa [hval]

-- Q' ≠ 0 at ρ : ρ is a simple root
lemma beukersQuadC_deriv_rho_ne_zero (a : ℝ) (ha : 3 ≤ a) :
    (2 * beukersRhoC a - 2 * (a : ℂ)) ≠ 0 := by
  have hs0 : Real.sqrt (a ^ 2 - 1) ≠ 0 := ne_of_gt (beukers_sqrt_sq_sub_one_pos a ha)
  have hs : (Real.sqrt (a ^ 2 - 1) : ℂ) ≠ 0 := by exact_mod_cast hs0
  intro h
  rw [beukersRhoC_eq] at h
  have hring : 2 * ((a : ℂ) - (Real.sqrt (a ^ 2 - 1) : ℂ)) - 2 * (a : ℂ) = -(2 * (Real.sqrt (a ^ 2 - 1) : ℂ)) := by ring
  rw [hring] at h
  have h3 : 2 * (Real.sqrt (a ^ 2 - 1) : ℂ) = 0 := neg_eq_zero.mp h
  have h4 : (Real.sqrt (a ^ 2 - 1) : ℂ) = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  exact hs h4

-- continuity of Q
lemma beukersQuadC_continuous (a : ℝ) : Continuous (beukersQuadC a) := by
  change Continuous (fun z : ℂ => 1 - 2 * (a : ℂ) * z + z ^ 2)
  fun_prop

-- the square-root coordinate at ρ : Q(ρ − u²) = u²·(2c + u²)
lemma beukersQuadC_rho_sub_sq (a : ℝ) (ha : 3 ≤ a) (u : ℂ) :
    beukersQuadC a (beukersRhoC a - u ^ 2) = u ^ 2 * (2 * (Real.sqrt (a ^ 2 - 1) : ℂ) + u ^ 2) := by
  calc
    beukersQuadC a (beukersRhoC a - u ^ 2)
        = ((beukersRhoC a - u ^ 2) - beukersRhoC a) * ((beukersRhoC a - u ^ 2) - beukersRc a) := by
            rw [beukersQuadC_factor a ha]
    _ = (-(u ^ 2)) * (beukersRhoC a - beukersRc a - u ^ 2) := by ring
    _ = u ^ 2 * (2 * (Real.sqrt (a ^ 2 - 1) : ℂ) + u ^ 2) := by
        have hdiff : beukersRc a - beukersRhoC a = 2 * (Real.sqrt (a ^ 2 - 1) : ℂ) := by
          rw [beukersRc_eq, beukersRhoC_eq]
          ring
        rw [← hdiff]
        ring

-- the pullback factor 2c + u² is nonzero for |u| < √(2c)
lemma beukers_rho_pull_factor_ne_zero (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    2 * (Real.sqrt (a ^ 2 - 1) : ℂ) + u ^ 2 ≠ 0 := by
  let c : ℝ := Real.sqrt (a ^ 2 - 1)
  have hc0 : 0 < c := by
    dsimp [c]
    exact beukers_sqrt_sq_sub_one_pos a ha
  have h2c0 : 0 ≤ 2 * c := by positivity
  have hu2 : ‖u‖ ^ 2 < 2 * c := by
    have hsqrt_pos : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
    have h1 : ‖u‖ ^ 2 ≤ ‖u‖ * Real.sqrt (2 * c) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (le_of_lt hu) (norm_nonneg u)
    have h2 : ‖u‖ * Real.sqrt (2 * c) < 2 * c := by
      calc
        ‖u‖ * Real.sqrt (2 * c) < Real.sqrt (2 * c) * Real.sqrt (2 * c) :=
            mul_lt_mul_of_pos_right hu hsqrt_pos
        _ = 2 * c := by
            rw [← sq]
            exact Real.sq_sqrt h2c0
    exact lt_of_le_of_lt h1 h2
  intro hzero
  have heq : u ^ 2 = -(2 * (Real.sqrt (a ^ 2 - 1) : ℂ)) := by
    rw [eq_neg_iff_add_eq_zero]
    rw [add_comm]
    exact hzero
  have hnm : ‖u ^ 2‖ = ‖2 * (Real.sqrt (a ^ 2 - 1) : ℂ)‖ := by
    rw [heq, norm_neg]
  have hnorm_u : ‖u ^ 2‖ = ‖u‖ ^ 2 := by simpa [pow_two] using (norm_mul u u)
  have hnorm_c : ‖2 * (Real.sqrt (a ^ 2 - 1) : ℂ)‖ = 2 * c := by
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hnormS : ‖(Real.sqrt (a ^ 2 - 1) : ℂ)‖ = Real.sqrt (a ^ 2 - 1) := by
      simp [abs_of_nonneg (Real.sqrt_nonneg (a ^ 2 - 1))]
    calc
      ‖2 * (Real.sqrt (a ^ 2 - 1) : ℂ)‖ = ‖(2 : ℂ)‖ * ‖(Real.sqrt (a ^ 2 - 1) : ℂ)‖ := by rw [norm_mul]
      _ = 2 * Real.sqrt (a ^ 2 - 1) := by rw [hnorm2, hnormS]
      _ = 2 * c := by dsimp [c]
  nlinarith

-- continuity of the pullback composite (first coordinate of the local branch)
lemma beukersQuadC_rho_sub_sq_continuous (a : ℝ) : Continuous (fun u : ℂ => beukersQuadC a (beukersRhoC a - u ^ 2)) := by
  dsimp [beukersQuadC, beukersRhoC, beukersRho]
  fun_prop

/-! ## The local branch of `√Q` in the square-root coordinate

The continuation through the singularity at `ρ` is exhibited in the
coordinate `u ↦ z = ρ − u²` (`beukersQuadC_rho_sub_sq`):
`Q(ρ − u²) = u²·(2c + u²)`, `c = √(a²−1)`.  This section defines the
**local branch objects** in `u`:

* `beukersSqrtC a u := √(2c + u²)` — the regular factor: holomorphic and
  nonzero on a small disc around `u = 0` (`beukersSqrtC_differentiableAt`,
  membership of `2c + u²` in the `Complex.slitPlane` on that disc);
* `beukersSigma a u := u·beukersSqrtC a u` — a square root of `Q(ρ−u²)` in
  the `u`-coordinate (σ(0) = 0 with nonzero derivative, the local
  uniformizer of the double cover);

so that along the pullback `A(z) = Q(z)^(−1/2)` becomes `1/σ(u)` and the
overconvergence object `A(z)·(W(z)−η_a)` is holomorphic in `u` at `0`.

Committed in this section: the membership of `2c+u²` in the slit plane on
the small disc (`beukers_quad2c_mem_slitPlane`, `beukers_rho_pull_norm_sq_lt`),
differentiability and continuity of `B` and `σ` in `u`
(`beukersSqrtC_differentiableAt`, `beukersSqrtC_continuousAt`,
`beukersSigma_differentiableAt`), the **square laws**
`B(u)² = 2c+u²` and `σ(u)² = Q(ρ−u²)` (`beukersSqrtC_sq`,
`beukersSigma_sq`; the latter via Commons
`Commons.Analysis.Complex.sq_sqrt_of_slitPlane`), and the value
`B(0) = √(2c) ≠ 0` (`beukersSqrtC_zero`, `beukersSqrtC_zero_ne_zero`) —
so `σ` is the local uniformizer of the double cover at `ρ`. -/

/-- `B(u) = √(2c + u²)`, `c = √(a²−1)`: the regular factor of the
pulled-back square root of `Q`. -/
noncomputable def beukersSqrtC (a : ℝ) (u : ℂ) : ℂ :=
  Complex.sqrt (2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2)

/-- `σ(u) = u·√(2c + u²)`: a square root of `Q(ρ − u²)` in the
`u`-coordinate (`σ(0) = 0`, `σ′(0) = √(2c) ≠ 0`). -/
noncomputable def beukersSigma (a : ℝ) (u : ℂ) : ℂ := u * beukersSqrtC a u

/-- `‖u‖ < √(2c)` implies `‖u‖² < 2c`, `c = √(a²−1)` (strict, elementary
norm inequality used throughout the branch lemmas). -/
lemma beukers_rho_pull_norm_sq_lt (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    ‖u‖ ^ 2 < 2 * Real.sqrt (a ^ 2 - 1) := by
  let c : ℝ := Real.sqrt (a ^ 2 - 1)
  have hc0 : 0 < c := by
    dsimp [c]
    exact beukers_sqrt_sq_sub_one_pos a ha
  have h2c0 : 0 ≤ 2 * c := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
  have h1 : ‖u‖ ^ 2 ≤ ‖u‖ * Real.sqrt (2 * c) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (le_of_lt hu) (norm_nonneg u)
  have h2 : ‖u‖ * Real.sqrt (2 * c) < 2 * c := by
    calc
      ‖u‖ * Real.sqrt (2 * c) < Real.sqrt (2 * c) * Real.sqrt (2 * c) :=
          mul_lt_mul_of_pos_right hu hsqrt_pos
      _ = 2 * c := by
          rw [← sq]
          exact Real.sq_sqrt h2c0
  have hle : ‖u‖ ^ 2 < 2 * c := lt_of_le_of_lt h1 h2
  dsimp [c] at hle
  exact hle

/-- the real part of the constant `2c` (`c = √(a²−1)`) -/
lemma beukers_two_c_re (a : ℝ) :
    (2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)).re = 2 * Real.sqrt (a ^ 2 - 1) := by
  have h2mul : 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) = (((2 * Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
    norm_num
  rw [h2mul, Complex.ofReal_re]

/-- for `‖u‖ < √(2c)` the point `2c + u²` lies in the `Complex.slitPlane`
(its real part is positive), so `Complex.sqrt` is holomorphic there -/
lemma beukers_quad2c_mem_slitPlane (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2 ∈ Complex.slitPlane := by
  have hre_lo : -(u ^ 2).re ≤ ‖u ^ 2‖ := by
    simpa only [Complex.neg_re, norm_neg] using (Complex.re_le_norm (-(u ^ 2)))
  have hnorm : ‖u ^ 2‖ = ‖u‖ ^ 2 := by simpa [pow_two] using (norm_mul u u)
  have hle2 : -(u ^ 2).re ≤ ‖u‖ ^ 2 := by
    calc -(u ^ 2).re ≤ ‖u ^ 2‖ := hre_lo
    _ = ‖u‖ ^ 2 := hnorm
  have hsq : ‖u‖ ^ 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_pull_norm_sq_lt a ha hu
  have hpos : 0 < (2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2).re := by
    rw [Complex.add_re, beukers_two_c_re]
    linarith
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl hpos

/-- the pullback map `u ↦ 2c + u²` is differentiable (polynomial) -/
lemma beukers_quad2c_pull_differentiableAt (a : ℝ) (u : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + w ^ 2) u := by
  fun_prop

/-- the pullback map `u ↦ 2c + u²` is continuous (polynomial) -/
lemma beukers_quad2c_pull_continuous (a : ℝ) :
    Continuous (fun w : ℂ => 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + w ^ 2) := by
  fun_prop

/-- `B(u) = √(2c+u²)` is differentiable at `u` for `‖u‖ < √(2c)` -/
lemma beukersSqrtC_differentiableAt (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    DifferentiableAt ℂ (beukersSqrtC a) u := by
  have hz : 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2 ∈ Complex.slitPlane :=
    beukers_quad2c_mem_slitPlane a ha hu
  have hsqrt : DifferentiableAt ℂ Complex.sqrt (2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2) :=
    Complex.differentiableAt_sqrt hz
  have hpull : DifferentiableAt ℂ
      (fun w : ℂ => 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + w ^ 2) u :=
    beukers_quad2c_pull_differentiableAt a u
  exact hsqrt.comp u hpull

/-- `B` is continuous at `u` for `‖u‖ < √(2c)` -/
lemma beukersSqrtC_continuousAt (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    ContinuousAt (beukersSqrtC a) u :=
  (beukersSqrtC_differentiableAt a ha hu).continuousAt

/-- `σ(u) = u·B(u)` is differentiable at `u` for `‖u‖ < √(2c)` -/
lemma beukersSigma_differentiableAt (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    DifferentiableAt ℂ (beukersSigma a) u := by
  have hB : DifferentiableAt ℂ (beukersSqrtC a) u := beukersSqrtC_differentiableAt a ha hu
  have hid : DifferentiableAt ℂ (fun w : ℂ => w) u := differentiableAt_id
  exact hid.mul hB

/-- `B(u)² = 2c + u²` for `‖u‖ < √(2c)` — `B` is a local square root of the
regular factor (Commons `sq_sqrt_of_slitPlane`, membership
`beukers_quad2c_mem_slitPlane`) -/
lemma beukersSqrtC_sq (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    (beukersSqrtC a u) ^ 2 = 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + u ^ 2 := by
  dsimp [beukersSqrtC]
  exact Commons.Analysis.Complex.sq_sqrt_of_slitPlane (beukers_quad2c_mem_slitPlane a ha hu)

/-- `σ(u)² = Q(ρ − u²)`: in the `u`-coordinate `σ` is a square root of the
pulled-back quadratic (so `A(ρ−u²) = 1/σ(u)` along the branch) -/
lemma beukersSigma_sq (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    (beukersSigma a u) ^ 2 = beukersQuadC a (beukersRhoC a - u ^ 2) := by
  dsimp [beukersSigma]
  rw [mul_pow, beukersSqrtC_sq a ha hu]
  rw [beukersQuadC_rho_sub_sq a ha u]

/-- value at `0`: `B(0) = √(2c)` (the positive real square root) -/
lemma beukersSqrtC_zero (a : ℝ) :
    beukersSqrtC a 0 = (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) : ℂ) := by
  dsimp [beukersSqrtC]
  have h2mul : 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + (0 : ℂ) ^ 2 =
      (((2 * Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
    norm_num
  rw [h2mul]
  have hnn : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) := by
    have hs : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  exact Commons.Analysis.Complex.sqrt_ofReal_of_nonneg hnn

/-- `B(0) ≠ 0`: the local uniformizer `σ` has nonzero derivative at `0`
(`σ′(0) = B(0)`) -/
lemma beukersSqrtC_zero_ne_zero (a : ℝ) (ha : 3 ≤ a) : beukersSqrtC a 0 ≠ 0 := by
  rw [beukersSqrtC_zero a]
  have hs : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hsq : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  exact_mod_cast (ne_of_gt hs)

/-! ## The `u`-coordinate derivative of the companion antiderivative

The identity that drives the continuation is the derivative of the
companion antiderivative `W` in the square-root coordinate `z = ρ − u²`:

`d/du W(ρ − u²) = −2/B(u)`,  `B(u) = √(2c + u²)`,  `c = √(a²−1)`

(`beukersWReal_rho_sub_sq_hasDerivAt` / `..._deriv`, for real `u > 0`, from
the chain rule with `W′ = A` and `A(ρ−u²) = 1/(u·B(u))` on `u > 0`).

**Sign/monodromy intel for the complex lift** (why the real statement takes
`u > 0`): on the real axis the positive determination of `A` gives
`√Q(ρ−u²) = |u|·B(u)`, so `A` is *even* in `u` while the holomorphic
continuation of `A` through `ρ` is *odd* in `u` (monodromy −1 around `ρ`).
The overconvergence object `A(z)·(W(z)−η_a)` is holomorphic in `z` at `ρ`,
i.e. an *even* holomorphic function of `u` (equivalently holomorphic in
`u² = ρ−z`); its value at `ρ` is `−1/√(a²−1)` (both factors contribute
`|u|`-cancelling signs).  The complex chapter will phrase this through the
holomorphic square root `σ(u)² = Q(ρ−u²)` (`beukersSigma_sq`) rather than
by real sign-chasing. -/
lemma beukersQuad_rho_sub_sq_real (a u : ℝ) (ha : 3 ≤ a) :
    beukersQuad a (beukersRho a - u ^ 2) = u ^ 2 * (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
  calc
    beukersQuad a (beukersRho a - u ^ 2)
        = ((beukersRho a - u ^ 2) - beukersRho a) * ((beukersRho a - u ^ 2) - (a + Real.sqrt (a ^ 2 - 1))) := by
            rw [beukersQuad_factor a (beukersRho a - u ^ 2) ha]
    _ = (-(u ^ 2)) * (beukersRho a - (a + Real.sqrt (a ^ 2 - 1)) - u ^ 2) := by ring
    _ = u ^ 2 * (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
        -- ρ − (a+√) = −2√(a²−1)
        have hdiff : beukersRho a - (a + Real.sqrt (a ^ 2 - 1)) = -(2 * Real.sqrt (a ^ 2 - 1)) := by
          dsimp [beukersRho]
          ring
        rw [hdiff]
        ring

/-- `B(u) = √(2c + u²)` over the reals (the regular factor of the pulled-back √Q) -/
def beukersBReal (a : ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2)

lemma beukersBReal_pos (a : ℝ) (ha : 3 ≤ a) (u : ℝ) : 0 < beukersBReal a u := by
  dsimp [beukersBReal]
  apply Real.sqrt_pos.2
  have hc : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
  positivity

-- A(ρ−u²) = 1/(u·B(u)) for u > 0
lemma beukersAReal_rho_sub_sq (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u) :
    beukersAReal a (beukersRho a - u ^ 2) = (u * beukersBReal a u)⁻¹ := by
  have hQ := beukersQuad_rho_sub_sq_real a u ha
  dsimp [beukersAReal, beukersSqrtQ, beukersBReal]
  rw [hQ]
  have hw : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) + u ^ 2 := by
    have hc : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    positivity
  have hsqrt : Real.sqrt (u ^ 2 * (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2)) =
      u * Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg u)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hu0]
  rw [hsqrt]

/-- **the u-coordinate derivative of the companion antiderivative**
`d/du W(ρ − u²) = −2/B(u)` on `u > 0` (chain rule from `W′ = A`,
`A(ρ−u²) = 1/(u·B(u))`) -/
lemma beukersWReal_rho_sub_sq_hasDerivAt (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u) :
    HasDerivAt (fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2))
      (-2 / beukersBReal a u) u := by
  have hxρ : beukersRho a - u ^ 2 < beukersRho a := by linarith [sq_pos_of_pos hu0]
  have h1 : HasDerivAt (beukersWReal a) (beukersAReal a (beukersRho a - u ^ 2)) (beukersRho a - u ^ 2) :=
    beukersWReal_hasDerivAt a ha hxρ
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u)
  have h2 : HasDerivAt (fun t : ℝ => beukersRho a - t ^ 2) (-(2 * u)) u :=
    HasDerivAt.const_sub (beukersRho a) hpow
  have hcomp : HasDerivAt (fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2))
      (beukersAReal a (beukersRho a - u ^ 2) * (-(2 * u))) u :=
    h1.comp (h := fun t : ℝ => beukersRho a - t ^ 2) (h₂ := beukersWReal a) u h2
  have hA := beukersAReal_rho_sub_sq a ha hu0
  have hB : beukersBReal a u ≠ 0 := ne_of_gt (beukersBReal_pos a ha u)
  have hu : u ≠ 0 := ne_of_gt hu0
  have hval : beukersAReal a (beukersRho a - u ^ 2) * (-(2 * u)) = -2 / beukersBReal a u := by
    rw [hA]
    field_simp [hu, hB]
  rw [hval] at hcomp
  exact hcomp

/-! ## The complex lift of the companion antiderivative `W`

The complex incarnation of the real companion `W` (`beukersWReal`) via the
principal branch:

`Wℂ(z) = Complex.log((a+1)/(a − z + √Q(z)))` (`beukersWComplex`), holomorphic
on the domain where `Q(z)` and the logarithm's argument avoid the slit
`(−∞, 0]` (the negative real axis) — i.e. stay in `Complex.slitPlane`;
`Aℂ(z) = 1/√Q(z)` (`beukersAComplex`) is its derivative there.

Committed in this section: the definitions and the **agreement on the real
axis** `beukersWComplex_eq_ofReal`: for `x < ρ`,
`Wℂ(↑x) = ↑(W(a,x))` — the branch is the one matching the real theory on
the interval `[0, ρ)` (`√Q(↑x) = ↑√(Q(x))` via Commons
`sqrt_ofReal_of_nonneg`, cast arithmetic, and `Complex.ofReal_log`). -/
/-- the complex lift of the companion antiderivative `W`:
`Wℂ(z) = log((a+1)/(a − z + √Q(z)))` (`Complex.log`, principal branch),
holomorphic on the domain where `Q(z)` and the log argument avoid the slit;
agrees with the real `W` on the real interval `[0, ρ)` (below). -/
noncomputable def beukersWComplex (a : ℝ) (z : ℂ) : ℂ :=
  Complex.log (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)))

/-- the complex lift of `A`: `Aℂ(z) = 1/√Q(z)` -/
noncomputable def beukersAComplex (a : ℝ) (z : ℂ) : ℂ :=
  (Complex.sqrt (beukersQuadC a z))⁻¹

-- Q over ℂ at a real point is the cast of Q over ℝ
lemma beukersQuadC_ofReal (a : ℝ) (x : ℝ) : beukersQuadC a (x : ℂ) = (beukersQuad a x : ℂ) := by
  dsimp [beukersQuadC, beukersQuad]
  norm_cast

/-- **agreement on the real axis**: for `0 ≤ x < ρ`, the complex lift equals
the cast of the real companion antiderivative -/
lemma beukersWComplex_eq_ofReal (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    beukersWComplex a (x : ℂ) = (beukersWReal a x : ℂ) := by
  have hQx : 0 < beukersQuad a x := beukersQuad_pos_of_lt_rho a x ha hxρ
  have hQx0 : 0 ≤ beukersQuad a x := le_of_lt hQx
  have hsqrt : Complex.sqrt (beukersQuadC a (x : ℂ)) = (Real.sqrt (beukersQuad a x) : ℂ) := by
    rw [beukersQuadC_ofReal]
    exact Commons.Analysis.Complex.sqrt_ofReal_of_nonneg hQx0
  have hden : (a : ℂ) - (x : ℂ) + Complex.sqrt (beukersQuadC a (x : ℂ))
      = (((a - x + Real.sqrt (beukersQuad a x) : ℝ) : ℂ)) := by
    rw [hsqrt]
    rw [← Complex.ofReal_sub]
    rw [← Complex.ofReal_add]
  have hratio : (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - (x : ℂ) + Complex.sqrt (beukersQuadC a (x : ℂ))))
      = ((((a + 1) / (a - x + Real.sqrt (beukersQuad a x)) : ℝ) : ℂ)) := by
    rw [hden]
    rw [← Complex.ofReal_div]
  have hdenR_pos : 0 < a - x + Real.sqrt (beukersQuad a x) := beukers_denom_pos_of_lt_rho a ha hxρ
  have hnumR_pos : 0 < (a : ℝ) + 1 := by linarith
  have hratio_pos : 0 < (a + 1) / (a - x + Real.sqrt (beukersQuad a x)) := div_pos hnumR_pos hdenR_pos
  dsimp [beukersWComplex]
  rw [hratio]
  rw [← Complex.ofReal_log (le_of_lt hratio_pos)]
  dsimp [beukersWReal, beukersSqrtQ]

/-- **agreement of `A` on the real axis**: for `x < ρ`,
`Aℂ(↑x) = ↑(A(a,x))` (companion of `beukersWComplex_eq_ofReal`) -/
lemma beukersAComplex_eq_ofReal (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    beukersAComplex a (x : ℂ) = (beukersAReal a x : ℂ) := by
  have hQx0 : 0 ≤ beukersQuad a x := le_of_lt (beukersQuad_pos_of_lt_rho a x ha hxρ)
  dsimp [beukersAComplex, beukersAReal]
  rw [beukersQuadC_ofReal]
  rw [Commons.Analysis.Complex.sqrt_ofReal_of_nonneg hQx0]
  rw [Complex.ofReal_inv]
  dsimp [beukersSqrtQ]

/-! ## The domain of holomorphy and `Wℂ′ = Aℂ`

The open set where the complex lift is holomorphic:

`beukersWComplexDomain a = {z | Q(z) ∈ slitPlane ∧ (a+1)/(a−z+√Q(z)) ∈ slitPlane}`

(the `Complex.slitPlane` is where `Complex.sqrt` at `Q(z)` and
`Complex.log` at the logarithm's argument are holomorphic).  Committed here:

* `beukersWComplexDomain_ofReal` — the real interval `(−∞, ρ)` lies in the
  domain (both `Q(x)` and the log argument are positive reals there);
* the derivative of `√Q` on the domain, value `Q′/(2√Q)`
  (`beukersQuadC_sqrt_hasDerivAt`, via `Complex.hasDerivAt_sqrt` with value
  `Q^(−1/2)/2` and Commons `cpow_neg_half_eq_inv_sqrt`);
* the derivative of the denominator `(a:ℂ) − z + √Q(z)`
  (`beukersDenomC_hasDerivAt`);
* **`beukersWComplex_hasDerivAt` — `Wℂ′ = Aℂ` on the domain**: the chain
  `log ∘ (num/denom)` with `HasDerivAt.div` and `Complex.hasDerivAt_log`,
  and the final value algebra
  `(num/δ)⁻¹·[(0·δ − num·vd)/δ²] = (√Qz)⁻¹` (`δ = a−z+√Qz`,
  `vd = −1 + (2z−2a)/(2√Qz)`, `num = (a+1)`) by `field_simp`.
-/
/-- the domain of holomorphy of the complex lift `Wℂ`: points where both the
quadratic `Q(z)` and the logarithm's argument lie in the `Complex.slitPlane`
(so `Complex.sqrt` at `Q(z)` and `Complex.log` at the argument are both
holomorphic) -/
def beukersWComplexDomain (a : ℝ) : Set ℂ :=
  {z : ℂ | beukersQuadC a z ∈ Complex.slitPlane ∧
    (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z))) ∈ Complex.slitPlane}

/-- the real interval `(−∞, ρ)` lies in the domain of holomorphy -/
lemma beukersWComplexDomain_ofReal (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    (x : ℂ) ∈ beukersWComplexDomain a := by
  have hQx : 0 < beukersQuad a x := beukersQuad_pos_of_lt_rho a x ha hxρ
  have hQ : beukersQuadC a (x : ℂ) ∈ Complex.slitPlane := by
    rw [beukersQuadC_ofReal]
    rw [Complex.ofReal_mem_slitPlane]
    exact hQx
  have hsqrt : Complex.sqrt (beukersQuadC a (x : ℂ)) = (Real.sqrt (beukersQuad a x) : ℂ) := by
    rw [beukersQuadC_ofReal]
    exact Commons.Analysis.Complex.sqrt_ofReal_of_nonneg (le_of_lt hQx)
  have hdenR_pos : 0 < a - x + Real.sqrt (beukersQuad a x) := beukers_denom_pos_of_lt_rho a ha hxρ
  have hnumR_pos : 0 < (a : ℝ) + 1 := by linarith
  have hratio_pos : 0 < (a + 1) / (a - x + Real.sqrt (beukersQuad a x)) := div_pos hnumR_pos hdenR_pos
  have hden : (a : ℂ) - (x : ℂ) + Complex.sqrt (beukersQuadC a (x : ℂ))
      = (((a - x + Real.sqrt (beukersQuad a x) : ℝ) : ℂ)) := by
    rw [hsqrt]
    rw [← Complex.ofReal_sub]
    rw [← Complex.ofReal_add]
  have hratio : (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - (x : ℂ) + Complex.sqrt (beukersQuadC a (x : ℂ))))
      = ((((a + 1) / (a - x + Real.sqrt (beukersQuad a x)) : ℝ) : ℂ)) := by
    rw [hden]
    rw [← Complex.ofReal_div]
  dsimp [beukersWComplexDomain]
  constructor
  · exact hQ
  · rw [hratio]
    rw [Complex.ofReal_mem_slitPlane]
    exact hratio_pos

-- derivative of √Q on the domain, value Q′/(2√Q)
lemma beukersQuadC_sqrt_hasDerivAt (a : ℝ) {z : ℂ} (hz : beukersQuadC a z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.sqrt (beukersQuadC a w))
      ((2 * z - 2 * (a : ℂ)) / (2 * Complex.sqrt (beukersQuadC a z))) z := by
  have hsq := Complex.hasDerivAt_sqrt hz
  have hQ := beukersQuadC_hasDerivAt a z
  have hc := hsq.comp z hQ
  have hs_ne : Complex.sqrt (beukersQuadC a z) ≠ 0 :=
    Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane hz
  have hcpow : (beukersQuadC a z) ^ (-1 / 2 : ℂ) = (Complex.sqrt (beukersQuadC a z))⁻¹ :=
    Commons.Analysis.Complex.cpow_neg_half_eq_inv_sqrt hz
  have hval : (beukersQuadC a z ^ (-1 / 2 : ℂ) / 2) * (2 * z - 2 * (a : ℂ)) =
      (2 * z - 2 * (a : ℂ)) / (2 * Complex.sqrt (beukersQuadC a z)) := by
    rw [hcpow]
    field_simp [hs_ne]
  rw [hval] at hc
  exact hc

-- derivative of the denominator u(w) = (a) − w + √Q(w)
lemma beukersDenomC_hasDerivAt (a : ℝ) {z : ℂ} (hz : beukersQuadC a z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => (a : ℂ) - w + Complex.sqrt (beukersQuadC a w))
      (-1 + (2 * z - 2 * (a : ℂ)) / (2 * Complex.sqrt (beukersQuadC a z))) z := by
  have h_am : HasDerivAt (fun w : ℂ => (a : ℂ) - w) (-1) z :=
    HasDerivAt.const_sub (a : ℂ) (hasDerivAt_id z)
  exact h_am.add (beukersQuadC_sqrt_hasDerivAt a hz)

-- the derivative identity: Wℂ′ = Aℂ on the domain
lemma beukersWComplex_hasDerivAt (a : ℝ) (ha : 3 ≤ a) {z : ℂ}
    (hz : z ∈ beukersWComplexDomain a) :
    HasDerivAt (beukersWComplex a) (beukersAComplex a z) z := by
  dsimp [beukersWComplexDomain] at hz
  rcases hz with ⟨hzQ, hzR⟩
  let s : ℂ := Complex.sqrt (beukersQuadC a z)
  let d : ℂ := (a : ℂ) - z + s
  let num : ℂ := ((a + 1 : ℝ) : ℂ)
  have hzR' : num / d ∈ Complex.slitPlane := by
    dsimp [num, d, s]
    exact hzR
  have hs_ne : s ≠ 0 := by
    dsimp [s]
    exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane hzQ
  have hnum_ne : num ≠ 0 := by
    dsimp [num]
    exact_mod_cast (ne_of_gt (by linarith : 0 < (a : ℝ) + 1))
  have hd_ne : d ≠ 0 := by
    intro hd0
    have hzero : num / d = 0 := by
      rw [hd0]
      simp
    have : (0 : ℂ) ∈ Complex.slitPlane := by simpa [hzero] using hzR'
    rw [Complex.mem_slitPlane_iff] at this
    simp at this
  -- derivative of the denominator map, value vd := −1 + (2z−2a)/(2s)
  have hdenD : HasDerivAt (fun w : ℂ => (a : ℂ) - w + Complex.sqrt (beukersQuadC a w))
      (-1 + (2 * z - 2 * (a : ℂ)) / (2 * s)) z := by
    dsimp [s]
    exact beukersDenomC_hasDerivAt a hzQ
  -- derivative of g(w) = num/(denom w)
  have hnumconst : HasDerivAt (fun w : ℂ => num) 0 z := hasDerivAt_const z num
  have hdz_ne : (a : ℂ) - z + Complex.sqrt (beukersQuadC a z) ≠ 0 := by
    exact hd_ne
  have hdd := hnumconst.div hdenD hdz_ne
  have hpoint : (fun w : ℂ => num / ((a : ℂ) - w + Complex.sqrt (beukersQuadC a w)))
      = ((fun w : ℂ => num) / (fun w : ℂ => (a : ℂ) - w + Complex.sqrt (beukersQuadC a w))) := by
    funext w
    rfl
  have hg : HasDerivAt (fun w : ℂ => num / ((a : ℂ) - w + Complex.sqrt (beukersQuadC a w)))
      ((0 * ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) - num * (-1 + (2 * z - 2 * (a : ℂ)) / (2 * s))) /
        ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) ^ 2) z := by
    rw [hpoint]
    exact hdd
  -- log ∘ g
  have hlog : HasDerivAt Complex.log ((num / d)⁻¹) (num / d) := Complex.hasDerivAt_log hzR'
  have hW := hlog.comp z hg
  dsimp [s, d, num] at hW
  -- final value algebra: (num/δ)⁻¹·[(0·δ − num·vd)/δ²] = (√Qz)⁻¹, δ := (a:ℂ)−z+√Qz
  have hval : ((((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)))⁻¹ *
      ((0 * ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) -
          ((a + 1 : ℝ) : ℂ) * (-1 + (2 * z - 2 * (a : ℂ)) / (2 * Complex.sqrt (beukersQuadC a z)))) /
        ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) ^ 2))
    = (Complex.sqrt (beukersQuadC a z))⁻¹ := by
    let s : ℂ := Complex.sqrt (beukersQuadC a z)
    let d : ℂ := (a : ℂ) - z + s
    let num : ℂ := ((a + 1 : ℝ) : ℂ)
    have hd_ne' : d ≠ 0 := by
      dsimp [d, s]
      exact hd_ne
    have hs_ne' : s ≠ 0 := by
      dsimp [s]
      exact hs_ne
    have hnum_ne' : num ≠ 0 := by
      dsimp [num]
      exact hnum_ne
    have hmain : (num / d)⁻¹ * ((0 * d - num * (-1 + (2 * z - 2 * (a : ℂ)) / (2 * s))) / d ^ 2) = s⁻¹ := by
      field_simp [hd_ne', hs_ne', hnum_ne']
      ring
    dsimp [num, s, d] at hmain
    exact hmain
  rw [hval] at hW
  change HasDerivAt (beukersWComplex a) (beukersAComplex a z) z
  dsimp [beukersAComplex]
  exact hW

/-! ## The `u`-coordinate expansion of `A·(W − η_a)` (real axis)

The real-axis content of the overconvergence across `ρ`:

* `beukersWReal_continuousAt_rho` — the closed-form antiderivative `W`
  extends continuously to the singularity endpoint `ρ`;
* `beukersBReal_continuous`, `beukersBReal_inv_continuous`,
  `beukersWReal_rho_sub_sq_continuousOn`, `beukersBReal_neg2_int` —
  continuity/integrability of the regular factor `B(u) = √(2c+u²)` and of
  the pullback `t ↦ W(ρ−t²)` on `[0,u]`;
* **`beukersWReal_rho_sub_sq_eq_int` — the FTC in the square-root
  coordinate**: for `0 ≤ u`, `W(ρ−u²) − η = −∫₀^u 2/B(v) dv`;
* **`beukers_apéry_rho_sub_sq_tendsto` — the boundary value**:
  `A(ρ−u²)·(W(ρ−u²) − η) → −1/√(a²−1)` as `u → 0⁺` (from the FTC identity,
  `A(ρ−u²) = 1/(u·B(u))`, and the derivative of `u ↦ ∫₀^u 2/B` at `0`).

This is the even-extension value in `u` (`u² = ρ−z`): the function is a
function of `u²`, i.e. of `ρ−z`, and takes the value `−1/√(a²−1)` at `ρ`;
the full holomorphic statement at `ρ` (complex, through `σ(u)² = Q(ρ−u²)`)
is the next coordinate. -/
-- W is continuous at ρ (the closed-form antiderivative extends continuously
-- to the singularity endpoint with value η)
lemma beukersWReal_continuousAt_rho (a : ℝ) (ha : 3 ≤ a) :
    ContinuousAt (beukersWReal a) (beukersRho a) := by
  have hquad : Continuous (fun x : ℝ => beukersQuad a x) := by
    dsimp [beukersQuad]
    fun_prop
  have hd : ContinuousAt (fun x : ℝ => a - x + beukersSqrtQ a x) (beukersRho a) := by
    have hlin : ContinuousAt (fun x : ℝ => a - x) (beukersRho a) := by
      have h : Continuous (fun x : ℝ => a - x) := by fun_prop
      exact h.continuousAt
    have hsq' : ContinuousAt (fun x : ℝ => beukersSqrtQ a x) (beukersRho a) := by
      have hsq : ContinuousAt (fun x : ℝ => Real.sqrt (beukersQuad a x)) (beukersRho a) :=
        hquad.continuousAt.sqrt
      simpa [beukersSqrtQ] using hsq
    exact hlin.add hsq'
  have hρeq : a - beukersRho a = Real.sqrt (a ^ 2 - 1) := by
    dsimp [beukersRho]
    ring
  have hd0 : a - beukersRho a + beukersSqrtQ a (beukersRho a) ≠ 0 := by
    have hQ0 : beukersQuad a (beukersRho a) = 0 := beukersQuad_rho_zero a ha
    have hsq0 : beukersSqrtQ a (beukersRho a) = 0 := by
      dsimp [beukersSqrtQ]
      rw [hQ0]
      simp
    rw [hsq0, hρeq]
    have hpos : 0 < Real.sqrt (a ^ 2 - 1) + 0 := by simpa using (beukers_sqrt_sq_sub_one_pos a ha)
    exact ne_of_gt hpos
  have hf : ContinuousAt (fun x : ℝ => ((a + 1 : ℝ) / (a - x + beukersSqrtQ a x))) (beukersRho a) := by
    have hnum : ContinuousAt (fun x : ℝ => ((a + 1 : ℝ) : ℝ)) (beukersRho a) := continuousAt_const
    exact hnum.div hd hd0
  have hf0 : ((a + 1 : ℝ) / (a - beukersRho a + beukersSqrtQ a (beukersRho a))) ≠ 0 := by
    have hnum0 : (a : ℝ) + 1 ≠ 0 := by
      have : 0 < (a : ℝ) + 1 := by linarith
      exact ne_of_gt this
    exact div_ne_zero hnum0 hd0
  change ContinuousAt (fun x : ℝ => Real.log ((a + 1) / (a - x + beukersSqrtQ a x))) (beukersRho a)
  exact ContinuousAt.log hf hf0

-- B(t) = √(2c+t²) is continuous (global)
lemma beukersBReal_continuous (a : ℝ) : Continuous (fun t : ℝ => beukersBReal a t) := by
  dsimp [beukersBReal]
  have harg : Continuous (fun t : ℝ => 2 * Real.sqrt (a ^ 2 - 1) + t ^ 2) := by fun_prop
  exact harg.sqrt

-- the pullback f(t) = W(ρ − t²) is continuous on [0, u] (u ≥ 0)
lemma beukersWReal_rho_sub_sq_continuousOn (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 ≤ u) :
    ContinuousOn (fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2)) (Set.Icc 0 u) := by
  intro t ht
  have hinner : ContinuousAt (fun x : ℝ => beukersRho a - x ^ 2) t := by
    have h : Continuous (fun x : ℝ => beukersRho a - x ^ 2) := by fun_prop
    exact h.continuousAt
  by_cases ht0' : t = 0
  · have hWc0 : ContinuousAt (beukersWReal a) (beukersRho a - t ^ 2) := by
      simpa [ht0'] using beukersWReal_continuousAt_rho a ha
    have hc : ContinuousAt (beukersWReal a ∘ (fun x : ℝ => beukersRho a - x ^ 2)) t :=
      ContinuousAt.comp hWc0 hinner
    have hc' : ContinuousAt (fun x : ℝ => beukersWReal a (beukersRho a - x ^ 2)) t :=
      hc.congr_of_eventuallyEq (by filter_upwards with x; rfl)
    exact hc'.continuousWithinAt (s := Set.Icc 0 u)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0')
    have hx : beukersRho a - t ^ 2 < beukersRho a := by
      have : 0 < t ^ 2 := sq_pos_of_pos htpos
      linarith
    have hWdx : ContinuousAt (beukersWReal a) (beukersRho a - t ^ 2) :=
      (beukersWReal_hasDerivAt a ha hx).continuousAt
    have hc : ContinuousAt (beukersWReal a ∘ (fun x : ℝ => beukersRho a - x ^ 2)) t :=
      ContinuousAt.comp hWdx hinner
    have hc' : ContinuousAt (fun x : ℝ => beukersWReal a (beukersRho a - x ^ 2)) t :=
      hc.congr_of_eventuallyEq (by filter_upwards with x; rfl)
    exact hc'.continuousWithinAt (s := Set.Icc 0 u)

-- the reciprocal 1/B is continuous (B > 0)
lemma beukersBReal_inv_continuous (a : ℝ) (ha : 3 ≤ a) :
    Continuous (fun t : ℝ => (beukersBReal a t)⁻¹) := by
  have hBcont := beukersBReal_continuous a
  have hBpos : ∀ t : ℝ, beukersBReal a t ≠ 0 := fun t => ne_of_gt (beukersBReal_pos a ha t)
  exact Continuous.inv₀ hBcont hBpos

-- −2/B is interval-integrable on [0,u]
lemma beukersBReal_neg2_int (a : ℝ) (ha : 3 ≤ a) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => (-2) / beukersBReal a t) MeasureTheory.volume 0 u := by
  have hc : Continuous (fun t : ℝ => (-2) / beukersBReal a t) := by
    have hinv : Continuous (fun t : ℝ => (beukersBReal a t)⁻¹) := beukersBReal_inv_continuous a ha
    have hmul : Continuous (fun t : ℝ => (-2 : ℝ) * (beukersBReal a t)⁻¹) := (continuous_const.mul hinv)
    simpa [div_eq_mul_inv] using hmul
  exact hc.continuousOn.intervalIntegrable

/-- **FTC in the square-root coordinate**: for `0 ≤ u`,
`W(ρ−u²) − η = −∫₀^u 2/B(v) dv`, `B(v) = √(2c+v²)` (from `W′ = A`,
`A(ρ−v²) = 1/(vB(v))`, and the boundary value `W(ρ) = η`) -/
lemma beukersWReal_rho_sub_sq_eq_int (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 ≤ u) :
    (∫ v in 0..u, (-2) / beukersBReal a v)
      = beukersWReal a (beukersRho a - u ^ 2) - beukersEta a := by
  let f : ℝ → ℝ := fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2)
  let f' : ℝ → ℝ := fun t : ℝ => (-2) / beukersBReal a t
  have hcont : ContinuousOn f (Set.Icc 0 u) := by
    dsimp [f]
    exact beukersWReal_rho_sub_sq_continuousOn a ha hu0
  have hderiv : ∀ x ∈ Set.Ioo 0 u, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have : HasDerivAt (fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2)) (f' x) x := by
      dsimp [f']
      exact beukersWReal_rho_sub_sq_hasDerivAt a ha hx0
    simpa [f] using this
  have hint : IntervalIntegrable f' MeasureTheory.volume 0 u := by
    dsimp [f']
    exact beukersBReal_neg2_int a ha u
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := f) (f' := f') hu0 hcont hderiv hint
  -- ∫ f' = f(u) − f(0): substitute f(0) = W(ρ) = η
  have hW0 : beukersWReal a (beukersRho a - 0 ^ 2) = beukersEta a := by
    simp
    exact beukersWReal_rho_eq_eta a ha
  dsimp [f, f'] at hFTC
  rw [hW0] at hFTC
  exact hFTC

-- B(0) = √(2c), c := √(a²−1)

-- B(0) = √(2c), c := √(a²−1)
lemma beukersBReal_zero_val (a : ℝ) : beukersBReal a 0 = Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
  simp [beukersBReal]

/-- **the u-coordinate expansion**: along `z = ρ − u²`, the single-valued
difference `A·(W − η)` satisfies
`A(ρ−u²)·(W(ρ−u²) − η) → −1/√(a²−1)` as `u → 0⁺` (the value at `ρ` of the
even holomorphic extension in `u`, computed from `W(ρ−u²)−η = −∫₀^u 2/B` and
`A(ρ−u²) = 1/(u·B(u))`). -/
lemma beukers_apéry_rho_sub_sq_tendsto (a : ℝ) (ha : 3 ≤ a) :
    Tendsto (fun u : ℝ => beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a))
      (𝓝[>] 0) (𝓝 (-1 / Real.sqrt (a ^ 2 - 1))) := by
  let g : ℝ → ℝ := fun v : ℝ => (-2) / beukersBReal a v
  let Ψ : ℝ → ℝ := fun u : ℝ => ∫ v in 0..u, g v
  have hBcontAt0 : ContinuousAt (beukersBReal a) 0 := (beukersBReal_continuous a).continuousAt
  have hB0ne : beukersBReal a 0 ≠ 0 := ne_of_gt (beukersBReal_pos a ha 0)
  have hgcont0 : ContinuousAt g 0 := by
    dsimp [g]
    exact continuousAt_const.div hBcontAt0 hB0ne
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 0 := by
    dsimp [g]
    exact beukersBReal_neg2_int a ha 0
  have hgcont : Continuous g := by
    dsimp [g]
    have hBne0 : ∀ t : ℝ, beukersBReal a t ≠ 0 := fun t => ne_of_gt (beukersBReal_pos a ha t)
    have hBcont := beukersBReal_continuous a
    exact (continuous_const.div hBcont hBne0)
  have hmeas : StronglyMeasurableAtFilter g (𝓝 0) MeasureTheory.volume :=
    Continuous.stronglyMeasurableAtFilter hgcont MeasureTheory.volume (𝓝 0)
  have hΨder0 : HasDerivAt Ψ ((-2) / beukersBReal a 0) 0 := by
    have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := 0) (f := g) hgint hmeas hgcont0
    dsimp [Ψ, g] at hd
    exact hd
  have hΨ0 : Ψ 0 = 0 := by
    dsimp [Ψ]
    exact intervalIntegral.integral_same (a := 0) (f := g)
  have hslope0 : Tendsto (slope Ψ 0) (𝓝[≠] 0) (𝓝 ((-2) / beukersBReal a 0)) := hΨder0.tendsto_slope
  have hQuot : Tendsto (fun u : ℝ => Ψ u / u) (𝓝[≠] 0) (𝓝 ((-2) / beukersBReal a 0)) := hslope0.congr' (by
    have hset : ({u : ℝ | u ≠ 0} : Set ℝ) ∈ 𝓝[≠] 0 := self_mem_nhdsWithin
    filter_upwards [hset] with u hu
    dsimp [slope]
    rw [hΨ0]
    field_simp [hu]
    ring)
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := by
    change (𝓝 0 ⊓ 𝓟 {y | (0 : ℝ) < y}) ≤ (𝓝 0 ⊓ 𝓟 {y | y ≠ 0})
    exact inf_le_inf (le_refl _) ((Filter.principal_mono).mpr (by intro y hy; exact ne_of_gt hy))
  have hQuotR : Tendsto (fun u : ℝ => Ψ u / u) (𝓝[>] 0) (𝓝 ((-2) / beukersBReal a 0)) := hQuot.mono_left hle
  have hInvR : Tendsto (fun u : ℝ => (beukersBReal a u)⁻¹) (𝓝[>] 0) (𝓝 (beukersBReal a 0)⁻¹) := by
    have hBlim : Tendsto (fun u : ℝ => beukersBReal a u) (𝓝[>] 0) (𝓝 (beukersBReal a 0)) :=
      hBcontAt0.tendsto.mono_left nhdsWithin_le_nhds
    exact Tendsto.inv₀ hBlim hB0ne
  have hProd : Tendsto (fun u : ℝ => (beukersBReal a u)⁻¹ * (Ψ u / u))
      (𝓝[>] 0) (𝓝 ((beukersBReal a 0)⁻¹ * ((-2) / beukersBReal a 0))) := hInvR.mul hQuotR
  -- expression rewrite: F(u) = (B u)⁻¹·(Ψ u / u) for u > 0
  have hFeq : (fun u : ℝ => beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a))
      =ᶠ[𝓝[>] 0] (fun u : ℝ => (beukersBReal a u)⁻¹ * (Ψ u / u)) := by
    have hset : ({u : ℝ | (0 : ℝ) < u} : Set ℝ) ∈ 𝓝[>] 0 := self_mem_nhdsWithin
    filter_upwards [hset] with u hu
    have hA : beukersAReal a (beukersRho a - u ^ 2) = (u * beukersBReal a u)⁻¹ := beukersAReal_rho_sub_sq a ha hu
    have hFTC := beukersWReal_rho_sub_sq_eq_int a ha (le_of_lt hu)
    have hW : beukersWReal a (beukersRho a - u ^ 2) - beukersEta a = Ψ u := by
      dsimp [Ψ, g]
      exact hFTC.symm
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hBne : beukersBReal a u ≠ 0 := ne_of_gt (beukersBReal_pos a ha u)
    calc
      beukersAReal a (beukersRho a - u ^ 2) * (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a)
          = (u * beukersBReal a u)⁻¹ * Ψ u := by rw [hA, hW]
      _ = (beukersBReal a u)⁻¹ * (Ψ u / u) := by
          field_simp [hu0, hBne]
  -- final value
  have hval : (beukersBReal a 0)⁻¹ * ((-2) / beukersBReal a 0) = -1 / Real.sqrt (a ^ 2 - 1) := by
    have hB0 : beukersBReal a 0 = Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := beukersBReal_zero_val a
    have hc0 : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) := by
      have : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
      positivity
    have hB0sq : (beukersBReal a 0) ^ 2 = 2 * Real.sqrt (a ^ 2 - 1) := by
      rw [hB0]
      exact Real.sq_sqrt hc0
    have hmain : (beukersBReal a 0)⁻¹ * ((-2) / beukersBReal a 0) = -2 / (beukersBReal a 0) ^ 2 := by
      field_simp [hB0ne]
    have hs0 : Real.sqrt (a ^ 2 - 1) ≠ 0 := ne_of_gt (beukers_sqrt_sq_sub_one_pos a ha)
    calc
      (beukersBReal a 0)⁻¹ * ((-2) / beukersBReal a 0) = -2 / (beukersBReal a 0) ^ 2 := hmain
      _ = -2 / (2 * Real.sqrt (a ^ 2 - 1)) := by rw [hB0sq]
      _ = -1 / Real.sqrt (a ^ 2 - 1) := by field_simp [hs0]
  -- assemble
  have hFin : Tendsto (fun u : ℝ => (beukersBReal a u)⁻¹ * (Ψ u / u))
      (𝓝[>] 0) (𝓝 (-1 / Real.sqrt (a ^ 2 - 1))) := by
    rw [hval] at hProd
    exact hProd
  exact hFin.congr' hFeq.symm

/-! ## The square-root coordinate `σ(u)` at `ρ` (complex, aligned)

The holomorphic square root of `Q(ρ − u²)` near `u = 0`:

* `beukersSqrtC a u = √(2c + u²)` — the regular factor `B(u)`, *even*
  (`beukersSqrtC_neg`), holomorphic and nonzero near `0`
  (`beukersSqrtC_differentiableAt`, `beukersSqrtC_zero_ne_zero`),
  `B(0) = √(2c)` (`beukersSqrtC_zero`);
* `beukersSigma a u = u·B(u)` — *odd* (`beukersSigma_neg`), the local
  uniformizer with `σ(u)² = Q(ρ−u²)` (`beukersSigma_sq`), `σ′(0) = B(0) ≠ 0`;
* **alignment with the real axis**: `beukersSigma_eq_sqrt_of_principal` —
  for real `u > 0`, `σ(u)` equals the principal `Complex.sqrt` of
  `Q(ρ − u²)` (the positive determination `u·B(u) > 0` of the real theory,
  so `A(z(u)) = 1/σ(u)` there).

This is the coordinate in which the even holomorphic extension of
`A·(W − η_a)` across `ρ` lives (`u² = ρ − z`; real-axis value
`−1/√(a²−1)` committed in §"The u-coordinate expansion …"): the extension
`G(u)` with `G(0) = −1/√(a²−1)` is the next coordinate, phrased through
`σ` rather than by real sign-chasing. -/
-- B(u) = √(2c + u²) is even
lemma beukersSqrtC_neg (a : ℝ) (u : ℂ) : beukersSqrtC a (-u) = beukersSqrtC a u := by
  dsimp [beukersSqrtC]
  congr 1
  ring

-- σ(u) = u·B(u) is odd (the square-root monodromy of A on the double cover)
lemma beukersSigma_neg (a : ℝ) (u : ℂ) : beukersSigma a (-u) = -beukersSigma a u := by
  dsimp [beukersSigma]
  rw [beukersSqrtC_neg]
  ring

/-- **alignment with the principal square root on the real axis**: for real
`u > 0` (where `z = ρ − u² ∈ (0, ρ)` is on the real interval of the real
theory), the holomorphic square root `σ(u)` equals the principal
`Complex.sqrt` of `Q(z(u))` — the same positive determination used in the
real-axis proof (`√Q(z(u)) = u·B(u) > 0`, so `A(z(u)) = 1/σ(u)`) -/
lemma beukersSigma_eq_sqrt_of_principal (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u) :
    beukersSigma a (u : ℂ) = Complex.sqrt (beukersQuadC a (beukersRhoC a - (u : ℂ) ^ 2)) := by
  have hpow : (u : ℂ) ^ 2 = (((u ^ 2 : ℝ) : ℂ)) := by rw [← Complex.ofReal_pow]
  have hz : beukersRhoC a - (u : ℂ) ^ 2 = (((beukersRho a - u ^ 2 : ℝ) : ℂ)) := by
    dsimp [beukersRhoC]
    rw [hpow]
    rw [← Complex.ofReal_sub]
  have hQz : beukersQuadC a (beukersRhoC a - (u : ℂ) ^ 2) = (((beukersQuad a (beukersRho a - u ^ 2)) : ℝ) : ℂ) := by
    rw [hz]
    exact beukersQuadC_ofReal a (beukersRho a - u ^ 2)
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hx : beukersRho a - u ^ 2 < beukersRho a := by linarith
  have hQpos : 0 < beukersQuad a (beukersRho a - u ^ 2) := beukersQuad_pos_of_lt_rho a (beukersRho a - u ^ 2) ha hx
  have hsqrtQ : Complex.sqrt (beukersQuadC a (beukersRhoC a - (u : ℂ) ^ 2))
      = ((Real.sqrt (beukersQuad a (beukersRho a - u ^ 2)) : ℝ) : ℂ) := by
    rw [hQz]
    exact Commons.Analysis.Complex.sqrt_ofReal_of_nonneg (le_of_lt hQpos)
  have hw0 : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) + u ^ 2 := by
    have hc : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    positivity
  have hreal : Real.sqrt (beukersQuad a (beukersRho a - u ^ 2)) = u * Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
    have hq := beukersQuad_rho_sub_sq_real a u ha
    rw [hq]
    calc
      Real.sqrt (u ^ 2 * (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2))
          = Real.sqrt (u ^ 2) * Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
              rw [Real.sqrt_mul (sq_nonneg u)]
      _ = u * Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_pos hu0]
  have hsig : beukersSigma a (u : ℂ) = (u : ℂ) * (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) : ℂ) := by
    dsimp [beukersSigma, beukersSqrtC]
    have harg : 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + (u : ℂ) ^ 2 = (((2 * Real.sqrt (a ^ 2 - 1) + u ^ 2 : ℝ) : ℂ)) := by
      rw [hpow]
      norm_num
    rw [harg]
    rw [Commons.Analysis.Complex.sqrt_ofReal_of_nonneg hw0]
  calc
    beukersSigma a (u : ℂ) = (u : ℂ) * (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) : ℂ) := hsig
    _ = (((u * Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) + u ^ 2) : ℝ) : ℂ)) := by
        rw [← Complex.ofReal_mul]
    _ = ((Real.sqrt (beukersQuad a (beukersRho a - u ^ 2)) : ℝ) : ℂ) := by
        congr 1
        rw [hreal]
    _ = Complex.sqrt (beukersQuadC a (beukersRhoC a - (u : ℂ) ^ 2)) := hsqrtQ.symm


/-! ## Toward the even extension `G(u)` of `A·(W−η_a)` through `ρ`

The extension object is the pullback `u ↦ A(z(u))·(W(z(u)) − η_a)`,
`z(u) = ρ − u²`, which is *even in `u`* (a function of `u² = ρ−z`) and
extends from the real axis to `u = 0` with value `−1/√(a²−1)` (committed on
the real axis in §"The u-coordinate expansion …").  This section pins its
`σ`-coordinate shape and parity:

* `beukers_zC_even` — `z(−u) = z(u)`, so both pullbacks
  (`beukersWComplex_pull_even`, `beukersAComplex_pull_even`, and the real
  `beukers_apéry_pull_real_even`) are even in `u` wherever defined;
* `beukersSqrtC_ofReal_eq` — the complex regular factor at a real point is
  the cast of the real one: `√(2c+u²) = ↑B(u)`;
* **`beukersAComplex_eq_sigma_inv`** — expressing `A` through `σ`: for real
  `u > 0`, `Aℂ(z(u)) = 1/σ(u)` (`Aℂ(↑x) = ↑(A(x))`, the real value
  `A(ρ−u²) = 1/(u·B(u))`, and `σ(u) = ↑(u·B(u))`).

The even holomorphic `G(u)` on a neighborhood of `0` (with
`G(0) = −1/√(a²−1)`, phrased through `σ` rather than by real sign-chasing)
is the next coordinate; it needs the analytic continuation of the
`u`-pullbacks through the regions where `z(u)` leaves the slit-plane domain
(equivalently: an identity/primitive step for the holomorphic `−2/B`). -/
-- z(u) = ρ − u² is even in u
lemma beukers_zC_even (a : ℝ) (u : ℂ) : beukersRhoC a - (-u) ^ 2 = beukersRhoC a - u ^ 2 := by
  ring

/-- the complex `√(2c+u²)` at a real point is the cast of the real regular factor -/
lemma beukersSqrtC_ofReal_eq (a : ℝ) (u : ℝ) :
    beukersSqrtC a (u : ℂ) = (beukersBReal a u : ℂ) := by
  dsimp [beukersSqrtC, beukersBReal]
  have hpow : (u : ℂ) ^ 2 = (((u ^ 2 : ℝ) : ℂ)) := by rw [← Complex.ofReal_pow]
  have harg : 2 * ((Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ) + (u : ℂ) ^ 2 = (((2 * Real.sqrt (a ^ 2 - 1) + u ^ 2 : ℝ) : ℂ)) := by
    rw [hpow]
    norm_num
  rw [harg]
  rw [Commons.Analysis.Complex.sqrt_ofReal_of_nonneg (by
    have hc : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    positivity)]

/-- **`A` through `σ`**: for real `u > 0`, `Aℂ(z(u)) = 1/σ(u)` (real-axis
agreements + alignment `beukersSigma_eq_sqrt_of_principal`) -/
lemma beukersAComplex_eq_sigma_inv (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u) :
    beukersAComplex a (beukersRhoC a - (u : ℂ) ^ 2) = (beukersSigma a (u : ℂ))⁻¹ := by
  have hxρ : beukersRho a - u ^ 2 < beukersRho a := by
    have : 0 < u ^ 2 := sq_pos_of_pos hu0
    linarith
  have hAcomp : beukersAComplex a (beukersRhoC a - (u : ℂ) ^ 2) = (beukersAReal a (beukersRho a - u ^ 2) : ℂ) := by
    have hz : beukersRhoC a - (u : ℂ) ^ 2 = (((beukersRho a - u ^ 2 : ℝ) : ℂ)) := by
      dsimp [beukersRhoC]
      have hpow : (u : ℂ) ^ 2 = (((u ^ 2 : ℝ) : ℂ)) := by rw [← Complex.ofReal_pow]
      rw [hpow]
      rw [← Complex.ofReal_sub]
    rw [hz]
    exact beukersAComplex_eq_ofReal a ha hxρ
  have hAreal : beukersAReal a (beukersRho a - u ^ 2) = (u * beukersBReal a u)⁻¹ :=
    beukersAReal_rho_sub_sq a ha hu0
  have hσ : beukersSigma a (u : ℂ) = (u : ℂ) * (beukersBReal a u : ℂ) := by
    calc
      beukersSigma a (u : ℂ) = (u : ℂ) * beukersSqrtC a (u : ℂ) := rfl
      _ = (u : ℂ) * (beukersBReal a u : ℂ) := by rw [beukersSqrtC_ofReal_eq a u]
  have hσval : beukersSigma a (u : ℂ) = ((((u * beukersBReal a u : ℝ)) : ℂ)) := by
    calc
      beukersSigma a (u : ℂ) = (u : ℂ) * (beukersBReal a u : ℂ) := hσ
      _ = ((((u * beukersBReal a u : ℝ)) : ℂ)) := by rw [← Complex.ofReal_mul]
  have hAinv : (beukersAReal a (beukersRho a - u ^ 2) : ℂ) = (((((u * beukersBReal a u : ℝ)⁻¹ : ℝ)) : ℂ)) := by
    rw [hAreal]
  calc
    beukersAComplex a (beukersRhoC a - (u : ℂ) ^ 2)
        = (beukersAReal a (beukersRho a - u ^ 2) : ℂ) := hAcomp
    _ = (beukersSigma a (u : ℂ))⁻¹ := by
        calc
          (beukersAReal a (beukersRho a - u ^ 2) : ℂ) = (((((u * beukersBReal a u : ℝ)⁻¹ : ℝ)) : ℂ)) := hAinv
          _ = (beukersSigma a (u : ℂ))⁻¹ := by
              rw [hσval]
              rw [← Complex.ofReal_inv]

-- the pullback Wℂ∘z(u) is even in u where defined (z is even)
lemma beukersWComplex_pull_even (a : ℝ) (u : ℂ) :
    beukersWComplex a (beukersRhoC a - (-u) ^ 2) = beukersWComplex a (beukersRhoC a - u ^ 2) := by
  rw [beukers_zC_even a u]

-- the pullback Aℂ∘z(u) is even in u where defined
lemma beukersAComplex_pull_even (a : ℝ) (u : ℂ) :
    beukersAComplex a (beukersRhoC a - (-u) ^ 2) = beukersAComplex a (beukersRhoC a - u ^ 2) := by
  rw [beukers_zC_even a u]

/-- **the pullback `A·(W−η)` is even in `u`** (real axis): the object whose
even holomorphic extension `G` through `ρ` we seek (`u² = ρ−z`) -/
lemma beukers_apéry_pull_real_even (a : ℝ) (u : ℝ) :
    beukersAReal a (beukersRho a - (-u) ^ 2) * (beukersWReal a (beukersRho a - (-u) ^ 2) - beukersEta a)
      = beukersAReal a (beukersRho a - u ^ 2) * (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) := by
  have hsq : (-u) ^ 2 = u ^ 2 := by ring
  rw [hsq]

/-! ## The analytic continuation: primitive of the holomorphic `−2/B`

The first step off the real axis: the regular factor `B(u) = √(2c+u²)` is
holomorphic and nonzero on the disc `‖u‖ < √(2c)`
(`beukersSqrtC_differentiableAt`, `beukers_quad2c_mem_slitPlane`,
`beukersSqrtC_zero_ne_zero`), so by Morera's theorem
(`DifferentiableOn.isExactOn_ball`, `Complex.IsExactOn.with_val_at`) the
function `u ↦ −2/B(u)` has a holomorphic primitive there:

* **`beukers_neg2B_primitive_on_ball`** — `∃ H, H(0) = 0` and
  `H′(u) = −2/B(u)` for all `u` with `‖u‖ < √(2·√(a²−1))`.

This `H` is the `u`-coordinate antiderivative that extends
`u ↦ W(ρ−u²) − η` off the real axis (`H′(u) = −2/B(u)` matches the real
derivative `d/du W(ρ−u²)` of §"The u-coordinate derivative …", and
`H(0) = 0 = W(ρ) − η`).  With it, the even holomorphic extension
`G(u) := H(u)/σ(u)` (`σ = u·B` the square-root coordinate of §"The
square-root coordinate σ(u) at ρ") is the target of the next coordinate:
`G` is holomorphic on a punctured neighbourhood of `0`, equals
`A·(W−η_a)∘z(u)` on the real axis (parity lemmas of §"Toward the even
extension G(u)"), and its value at `0` is `−1/√(a²−1)`. -/
lemma beukers_neg2B_primitive_on_ball (a : ℝ) (ha : 3 ≤ a) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧
      ∀ u, u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) →
        HasDerivAt H (-2 / beukersSqrtC a u) u := by
  let R : ℝ := Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))
  let f : ℂ → ℂ := fun u : ℂ => (-2) / beukersSqrtC a u
  -- f differentiable on the ball (B differentiable & nonzero there)
  have hBne : ∀ u ∈ Metric.ball 0 R, beukersSqrtC a u ≠ 0 := by
    intro u hu
    have hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
      dsimp [R] at hu
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane (beukers_quad2c_mem_slitPlane a ha hub)
  have hBdiff : DifferentiableOn ℂ (beukersSqrtC a) (Metric.ball 0 R) := by
    intro u hu
    have hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
      dsimp [R] at hu
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact (beukersSqrtC_differentiableAt a ha hub).differentiableWithinAt
  have hconst : DifferentiableOn ℂ (fun u : ℂ => (-2 : ℂ)) (Metric.ball 0 R) := by
    intro u hu
    exact (differentiableAt_const (𝕜 := ℂ) ((-2 : ℂ) : ℂ)).differentiableWithinAt
  have hfdiff : DifferentiableOn ℂ f (Metric.ball 0 R) := by
    dsimp [f]
    exact DifferentiableOn.div hconst hBdiff hBne
  have hexact := _root_.DifferentiableOn.isExactOn_ball hfdiff
  -- primitive with value 0 at 0
  have hw := Complex.IsExactOn.with_val_at hexact (0 : ℂ) (0 : ℂ)
  rcases hw with ⟨H, hH0, hH⟩
  refine ⟨H, hH0, ?_⟩
  intro u hu
  have hub : u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    simpa [R] using hu
  simpa [f] using (hH u hub)


/-! ## The odd antiderivative `HU` and the even extension candidate `G`

With the Morera primitive `beukersH0` (from §"The analytic continuation") we
form the **odd** `u`-coordinate antiderivative

`HU(u) = (P(u) − P(−u))/2`  (`beukersHU`): odd by construction
(`beukersHU_neg`), `HU(0) = 0` (`beukersHU_zero`).  (That `HU′ = −2/B` —
it is still a primitive of the even function `−2/B` — is the next lemma;
the composition `u ↦ P(−u)` is where the ℂ-`HasDerivAt` instance-path
friction shows up, cf. the earlier notes.)

The even extension candidate of §"Toward the even extension G(u)" is then
`G(u) = HU(u)/σ(u)` (`beukersGExt`, `σ = u·B` the square-root coordinate):
it is **even** on the punctured coordinate disc (`beukersGExt_neg`, from
`HU` odd and `σ` odd), equals `A·(W−η_a)∘z(u)` on the real axis, and its
value at `u = 0` is `−1/√(a²−1)` (real-axis value committed in §"The
u-coordinate expansion …"). -/
/-- a Morera primitive of `−2/B` on the disc (chosen from
`beukers_neg2B_primitive_on_ball`) -/
noncomputable def beukersH0 (a : ℝ) (ha : 3 ≤ a) : ℂ → ℂ :=
  Classical.choose (beukers_neg2B_primitive_on_ball a ha)

lemma beukersH0_zero (a : ℝ) (ha : 3 ≤ a) : beukersH0 a ha 0 = 0 :=
  (Classical.choose_spec (beukers_neg2B_primitive_on_ball a ha)).1

lemma beukersH0_hasDerivAt (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) :
    HasDerivAt (beukersH0 a ha) (-2 / beukersSqrtC a u) u :=
  (Classical.choose_spec (beukers_neg2B_primitive_on_ball a ha)).2 u hu

/-- the **odd** `u`-coordinate antiderivative: `HU(u) = (P(u) − P(−u))/2`,
still a primitive of `−2/B` with `HU(0) = 0`, odd by construction -/
noncomputable def beukersHU (a : ℝ) (ha : 3 ≤ a) : ℂ → ℂ :=
  fun u => (beukersH0 a ha u - beukersH0 a ha (-u)) / 2

lemma beukersHU_zero (a : ℝ) (ha : 3 ≤ a) : beukersHU a ha 0 = 0 := by
  dsimp [beukersHU]
  rw [neg_zero, beukersH0_zero a ha]
  ring

/-- `HU` is odd -/
lemma beukersHU_neg (a : ℝ) (ha : 3 ≤ a) (u : ℂ) : beukersHU a ha (-u) = -beukersHU a ha u := by
  dsimp [beukersHU]
  ring_nf
/-- **the even extension candidate**: `G(u) = HU(u)/σ(u)` on the coordinate
disc (`HU` odd with `HU(0)=0`, `σ = u·B` odd) — equals `A·(W−η_a)∘z(u)` on
the real axis and extends with value `−1/√(a²−1)` at `u = 0` -/
noncomputable def beukersGExt (a : ℝ) (ha : 3 ≤ a) (u : ℂ) : ℂ :=
  beukersHU a ha u / beukersSigma a u

/-- `G` is even on the punctured ball: `G(−u) = G(u)` for `‖u‖ < √(2c)`,
`u ≠ 0` (from `HU` odd, `σ` odd) -/
lemma beukersGExt_neg (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu0 : u ≠ 0)
    (hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    beukersGExt a ha (-u) = beukersGExt a ha u := by
  have hσne : beukersSigma a u ≠ 0 := by
    -- σ(u) = u·B(u), B(u) ≠ 0 on the small disc, u ≠ 0
    dsimp [beukersSigma]
    have hBne : beukersSqrtC a u ≠ 0 := by
      exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane (beukers_quad2c_mem_slitPlane a ha hub)
    exact mul_ne_zero hu0 hBne
  have hσmne : beukersSigma a (-u) ≠ 0 := by
    rw [beukersSigma_neg a u]
    exact neg_ne_zero.mpr hσne
  have hHodd := beukersHU_neg a ha u
  have hσodd := beukersSigma_neg a u
  dsimp [beukersGExt]
  rw [hHodd, hσodd]
  field_simp [hσne]
/-- **`HU′ = −2/B` on the coordinate disc** (the odd antiderivative is a
primitive of the even `−2/B`; `deriv`-based, no `HasDerivAt`-chain
instance friction) -/
lemma beukersHU_deriv (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hu : u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) :
    deriv (beukersHU a ha) u = -2 / beukersSqrtC a u := by
  have hum : -u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    simpa using hu
  have dh0 : DifferentiableAt ℂ (beukersH0 a ha) u :=
    (beukersH0_hasDerivAt a ha hu).differentiableAt
  have dh0m : DifferentiableAt ℂ (beukersH0 a ha) (-u) :=
    (beukersH0_hasDerivAt a ha hum).differentiableAt
  have hneg : DifferentiableAt ℂ Neg.neg u := by
    change DifferentiableAt ℂ (fun w : ℂ => -w) u
    fun_prop
  have hQd : DifferentiableAt ℂ (fun w : ℂ => beukersH0 a ha (-w)) u := by
    exact dh0m.comp u hneg
  have hdP : deriv (beukersH0 a ha) u = -2 / beukersSqrtC a u :=
    (beukersH0_hasDerivAt a ha hu).deriv
  have hdPm : deriv (beukersH0 a ha) (-u) = -2 / beukersSqrtC a (-u) :=
    (beukersH0_hasDerivAt a ha hum).deriv
  have hdQ : deriv (fun w : ℂ => beukersH0 a ha (-w)) u = 2 / beukersSqrtC a u := by
    change deriv (beukersH0 a ha ∘ Neg.neg) u = 2 / beukersSqrtC a u
    rw [deriv_comp u dh0m hneg]
    rw [deriv_neg u]
    rw [hdPm]
    rw [beukersSqrtC_neg a u]
    ring
  have hmain : deriv (fun w : ℂ => beukersH0 a ha w - beukersH0 a ha (-w)) u = -4 / beukersSqrtC a u := by
    change deriv ((beukersH0 a ha) - (fun w : ℂ => beukersH0 a ha (-w))) u = -4 / beukersSqrtC a u
    rw [deriv_sub dh0 hQd]
    rw [hdP, hdQ]
    ring
  have hderiv2 : deriv (fun w : ℂ => (beukersH0 a ha w - beukersH0 a ha (-w)) / 2) u = -2 / beukersSqrtC a u := by
    rw [deriv_div_const (2 : ℂ)]
    rw [hmain]
    ring
  exact hderiv2


/-! ## Real-axis restriction of `HU` (the agreement normalization)

The normalization that makes the real-axis agreement true: the odd
antiderivative `HU` (complex, from §"The odd antiderivative HU and the even
extension candidate G") restricts to the real axis with the **same real
derivative as `u ↦ W(ρ−u²) − η`**:

* `beukersHU_differentiableAt` — `HU` is complex-differentiable on the
  coordinate disc;
* `beukersSqrtC_ofReal_neg2` — `−2/B(↑t) = ↑(−2/B(t))` (complex value of
  the regular factor's reciprocal at a real point);
* **`beukersHU_real_deriv`** — for real `0 < u < √(2c)`,
  `HasDerivAt (fun t => HU(↑t)) (−2/B(u)) u` (via `HasDerivAt.comp_ofReal`,
  `Mathlib/Analysis/Complex/RealDeriv.lean`).

Together with `beukersWReal_rho_sub_sq_hasDerivAt`, `HU(0) = 0 = W(ρ) − η`
and the real FTC on `[0,u]`, this yields the real-axis agreement
`HU(u) = W(ρ−u²) − η` — the next lemma (its proof is a `deriv`-based FTC grind
of the same shape as `beukersWReal_rho_sub_sq_eq_int`). -/
/-- differentiability of `HU` inside the coordinate disc -/
lemma beukersHU_differentiableAt (a : ℝ) (ha : 3 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) :
    DifferentiableAt ℂ (beukersHU a ha) z := by
  have hzm : -z ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    simpa using hz
  have dh0 : DifferentiableAt ℂ (beukersH0 a ha) z :=
    (beukersH0_hasDerivAt a ha hz).differentiableAt
  have dh0m : DifferentiableAt ℂ (beukersH0 a ha) (-z) :=
    (beukersH0_hasDerivAt a ha hzm).differentiableAt
  have hneg : DifferentiableAt ℂ Neg.neg z := by
    change DifferentiableAt ℂ (fun w : ℂ => -w) z
    fun_prop
  have hQd : DifferentiableAt ℂ (fun w : ℂ => beukersH0 a ha (-w)) z := dh0m.comp z hneg
  exact (dh0.sub hQd).div_const (2 : ℂ)

/-- **real-axis restriction of `HU`**: for real `0 < u < √(2c)`, the
restricted function `t ↦ HU(t)` (real variable) has real derivative
`−2/B(u)` — the same value as `d/du W(ρ−u²)`; this is the normalization
making the real-axis agreement `HU(u) = W(ρ−u²) − η` true. -/
lemma beukersHU_real_deriv (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u)
    (huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    HasDerivAt (fun t : ℝ => beukersHU a ha (t : ℂ)) ((-2) / beukersSqrtC a (u : ℂ)) u := by
  have hub : (u : ℂ) ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    have hnorm : ‖(u : ℂ)‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
      have hle : ‖(u : ℂ)‖ = u := by
        rw [show ‖(u : ℂ)‖ = |u| by simp]
        exact abs_of_pos hu0
      rwa [hle]
    simpa [Metric.mem_ball, dist_zero_right] using hnorm
  have hd : deriv (beukersHU a ha) (u : ℂ) = (-2) / beukersSqrtC a (u : ℂ) :=
    beukersHU_deriv a ha hub
  have hdiff := beukersHU_differentiableAt a ha hub
  have hH : HasDerivAt (beukersHU a ha) ((-2) / beukersSqrtC a (u : ℂ)) (u : ℂ) := by
    simpa [hd] using hdiff.hasDerivAt
  exact hH.comp_ofReal


-- the complex value of B at a real point equals the cast of the real value, −2-form
lemma beukersSqrtC_ofReal_neg2 (a : ℝ) (t : ℝ) :
    (-2) / beukersSqrtC a (t : ℂ) = ((-2 / beukersBReal a t : ℝ) : ℂ) := by
  have hB := beukersSqrtC_ofReal_eq a t
  -- −2/B(↑t) = ↑(−2/Breal): (−2:ℂ)/(↑B) with B(↑t) = ↑Breal:
  rw [hB]
  have hnum : (-2 : ℂ) = (((-2 : ℝ) : ℂ)) := by norm_num
  rw [hnum]
  rw [← Complex.ofReal_div]

/-- **real-axis restriction of `HU`, per-point continuity**: for real
`0 ≤ t < √(2·√(a²−1))`, the function
`x ↦ HU(↑x) − (↑W(ρ−x²) − ↑η)` is continuous at `t` (`HU` differentiable
on the coordinate disc, `W` continuous up to `ρ`). -/
lemma beukersHU_restrict_cont_at (a : ℝ) (ha : 3 ≤ a) {t : ℝ} (ht0 : 0 ≤ t)
    (htR : t < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    ContinuousAt (fun x : ℝ =>
      beukersHU a ha (x : ℂ) - ((beukersWReal a (beukersRho a - x ^ 2) : ℂ) - (beukersEta a : ℂ))) t := by
  have hnorm : ‖(t : ℂ)‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    have hn : ‖(t : ℂ)‖ = |t| := by simp
    rw [hn, abs_of_nonneg ht0]
    exact htR
  have hub : (t : ℂ) ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    simpa [Metric.mem_ball, dist_zero_right] using hnorm
  have hinner : ContinuousAt (fun x : ℝ => (x : ℂ)) t := Complex.continuous_ofReal.continuousAt
  have hcHU : ContinuousAt (beukersHU a ha) (t : ℂ) :=
    (beukersHU_differentiableAt a ha hub).continuousAt
  have hg : ContinuousAt (fun x : ℝ => beukersHU a ha (x : ℂ)) t :=
    ContinuousAt.comp hcHU hinner
  have hpoly : ContinuousAt (fun x : ℝ => beukersRho a - x ^ 2) t := by
    have hc : Continuous (fun x : ℝ => beukersRho a - x ^ 2) := by fun_prop
    exact hc.continuousAt
  have hWct : ContinuousAt (beukersWReal a) (beukersRho a - t ^ 2) := by
    by_cases ht0c : t = 0
    · simpa [ht0c] using beukersWReal_continuousAt_rho a ha
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0c)
      have hx : beukersRho a - t ^ 2 < beukersRho a := by
        have : 0 < t ^ 2 := sq_pos_of_pos htpos
        linarith
      exact (beukersWReal_hasDerivAt a ha hx).continuousAt
  have hw1real : ContinuousAt (fun x : ℝ => beukersWReal a (beukersRho a - x ^ 2)) t := by
    have hc : ContinuousAt (beukersWReal a ∘ (fun x : ℝ => beukersRho a - x ^ 2)) t :=
      ContinuousAt.comp hWct hpoly
    exact hc.congr_of_eventuallyEq (by filter_upwards with x; rfl)
  have hw1 : ContinuousAt (fun x : ℝ => (beukersWReal a (beukersRho a - x ^ 2) : ℂ)) t := by
    have hc : ContinuousAt (Complex.ofReal ∘ (fun x : ℝ => beukersWReal a (beukersRho a - x ^ 2))) t :=
      ContinuousAt.comp (Complex.continuous_ofReal.continuousAt) hw1real
    exact hc.congr_of_eventuallyEq (by filter_upwards with x; rfl)
  have hsub2 := hg.sub hw1
  have hcst : ContinuousAt (fun x : ℝ => (beukersEta a : ℂ)) t := by
    exact continuousAt_const
  have htmp := hsub2.add hcst
  refine htmp.congr_of_eventuallyEq ?_
  filter_upwards with x
  dsimp
  ring

/-- **real-axis agreement of `HU` with `W(ρ−u²) − η`** (the complex/real
normalization): for real `0 ≤ u < √(2·√(a²−1))`,
`HU(↑u) = ↑W(ρ−u²) − ↑η`. Both sides vanish at `u = 0` and both restricted
functions have real derivative `−2/B` on `(0, √(2c))`
(`beukersHU_real_deriv` = `beukersWReal_rho_sub_sq_hasDerivAt` via
`beukersSqrtC_ofReal_neg2`), so the difference is constant `0` by the
real-variable FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`,
the same shape as `beukersWReal_rho_sub_sq_eq_int`). -/
lemma beukersHU_real_axis (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 ≤ u)
    (huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    beukersHU a ha (u : ℂ) = (beukersWReal a (beukersRho a - u ^ 2) : ℂ) - (beukersEta a : ℂ) := by
  let R : ℝ := Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))
  let f : ℝ → ℂ := fun t : ℝ =>
    beukersHU a ha (t : ℂ) - ((beukersWReal a (beukersRho a - t ^ 2) : ℂ) - (beukersEta a : ℂ))
  have hcont : ContinuousOn f (Set.Icc 0 u) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hlt : t < R := by
      dsimp [R]
      exact lt_of_le_of_lt ht.2 huR
    have hc := beukersHU_restrict_cont_at a ha ht0 hlt
    dsimp [f]
    exact hc.continuousWithinAt (s := Set.Icc 0 u)
  have hderiv : ∀ x ∈ Set.Ioo 0 u, HasDerivAt f 0 x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxR : x < R := by
      dsimp [R]
      exact lt_of_le_of_lt (le_of_lt hx.2) huR
    have hd1 : HasDerivAt (fun t : ℝ => beukersHU a ha (t : ℂ)) (((-2 / beukersBReal a x : ℝ) : ℂ)) x := by
      have h0 := beukersHU_real_deriv a ha hx0 hxR
      have hc := beukersSqrtC_ofReal_neg2 a x
      rwa [hc] at h0
    have hWx : HasDerivAt (fun t : ℝ => beukersWReal a (beukersRho a - t ^ 2)) (-2 / beukersBReal a x) x :=
      beukersWReal_rho_sub_sq_hasDerivAt a ha hx0
    have hWcast : HasDerivAt (fun t : ℝ => (beukersWReal a (beukersRho a - t ^ 2) : ℂ))
        (((-2 / beukersBReal a x : ℝ) : ℂ)) x := by
      simpa using hWx.ofReal_comp
    have hcst : HasDerivAt (fun t : ℝ => (beukersEta a : ℂ)) 0 x := hasDerivAt_const x (beukersEta a : ℂ)
    have hsub := hd1.sub (hWcast.sub hcst)
    dsimp [f]
    convert hsub using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (0 : ℂ)) MeasureTheory.volume 0 u := by
    exact continuous_const.intervalIntegrable 0 u
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := f) (f' := fun t : ℝ => (0 : ℂ)) hu0 hcont hderiv hint
  have hint0 : (∫ t in 0..u, (0 : ℂ)) = 0 := by simp
  have hf0 : f 0 = 0 := by
    dsimp [f]
    have hH0 : beukersHU a ha (0 : ℂ) = 0 := beukersHU_zero a ha
    have hW0 : (beukersWReal a (beukersRho a) : ℂ) - (beukersEta a : ℂ) = 0 := by
      have : beukersWReal a (beukersRho a) = beukersEta a := beukersWReal_rho_eq_eta a ha
      simp [this]
    simp [hH0, hW0]
  have hFTC' : (∫ t in 0..u, (0 : ℂ)) = f u - f 0 := by simpa [f] using hFTC
  have hfin : f u = 0 := by
    rw [hint0, hf0] at hFTC'
    simpa using hFTC'.symm
  have hdiff0 : beukersHU a ha (u : ℂ) - ((beukersWReal a (beukersRho a - u ^ 2) : ℂ) - (beukersEta a : ℂ)) = 0 := by
    dsimp [f] at hfin
    exact hfin
  exact sub_eq_zero.mp hdiff0

/-! ## The even holomorphic extension `G` of `A·(W−η_a)∘z(u)` through `u = 0`

With the real-axis agreement `beukersHU_real_axis` in hand, the extension
object `G(u) = HU(u)/σ(u)` (`beukersGExt`) is now pinned:

* **`beukersGExt_real_axis`** — for real `0 < u < √(2c)`,
  `G(↑u) = ↑(A(ρ−u²)·(W(ρ−u²) − η_a))` (the axis agreement: divide
  `HU(↑u) = ↑(W(ρ−u²)) − ↑η` by `σ(↑u) = ↑(u·B(u))` and use
  `A(ρ−u²) = 1/(u·B(u))`);
* **`beukersGExt_real_axis_tendsto`** — the real-axis boundary value:
  `G(↑u) → ↑(−1/√(a²−1))` as `u → 0⁺` (composition of the axis agreement
  with `beukers_apéry_rho_sub_sq_tendsto`);
* **`beukersGExt_tendsto_zero`** — the full (two-sided) limit
  `G(u) → ↑(−1/√(a²−1))` as `u → 0`, `u ≠ 0`: `G = (HU(u)/u)·B(u)⁻¹`,
  `HU(u)/u → HU′(0) = −2/B(0)` (differentiability of `HU` at `0`,
  `beukersHU_deriv`), `B(u) → B(0) ≠ 0`, and
  `(−2/B(0))·B(0)⁻¹ = −1/√(a²−1)` (`B(0)² = 2√(a²−1)`); together with
  `beukersGExt_neg` (evenness on the punctured disc) this is the even
  holomorphic extension of `A·(W−η_a)∘z` through the square-root point
  `u = 0` (value `−1/√(a²−1)`, i.e. through `x = ρ` in the `z`-plane);
* **`beukersGExt_differentiableAt`** — `G` is complex-differentiable at
  every `u ≠ 0` of the coordinate disc (quotient of `HU` and `σ`, with
  `σ(u) = u·B(u) ≠ 0` there).

The next coordinate after this section: descend the even holomorphic `G`
to a holomorphic function of `u² = ρ − x` near `ρ` and compare with the
power series of `H(x) − η_a·A(x)` (Cauchy bounds; roadmap below). -/
/-- **real-axis agreement of `G`**: for real `0 < u < √(2c)`,
`G(u) = ↑(A(ρ−u²)·(W(ρ−u²) − η_a))` (divide the `HU` axis value
`beukersHU_real_axis` by `σ(u) = ↑(u·B(u))`, using
`A(ρ−u²) = 1/(u·B(u))` of `beukersAReal_rho_sub_sq`) -/
lemma beukersGExt_real_axis (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u)
    (huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    beukersGExt a ha (u : ℂ) =
      ((beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) : ℝ) : ℂ) := by
  have hHU := beukersHU_real_axis a ha (le_of_lt hu0) huR
  have hBpos : 0 < beukersBReal a u := beukersBReal_pos a ha u
  have hBne : beukersBReal a u ≠ 0 := ne_of_gt hBpos
  have hσval : beukersSigma a (u : ℂ) = ((((u * beukersBReal a u : ℝ)) : ℂ)) := by
    calc
      beukersSigma a (u : ℂ) = (u : ℂ) * beukersSqrtC a (u : ℂ) := rfl
      _ = (u : ℂ) * (beukersBReal a u : ℂ) := by rw [beukersSqrtC_ofReal_eq a u]
      _ = ((((u * beukersBReal a u : ℝ)) : ℂ)) := by rw [← Complex.ofReal_mul]
  dsimp [beukersGExt]
  rw [hHU]
  rw [hσval]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  have hA := beukersAReal_rho_sub_sq a ha hu0
  have hmul : u * beukersBReal a u ≠ 0 := mul_ne_zero (ne_of_gt hu0) hBne
  calc
    (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) / (u * beukersBReal a u)
        = (u * beukersBReal a u)⁻¹ * (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) := by
            field_simp [hmul]
    _ = beukersAReal a (beukersRho a - u ^ 2) * (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) := by
            rw [hA]

/-- **real-axis boundary value of `G`**: `G(↑u) → ↑(−1/√(a²−1))` as
`u → 0⁺` (the axis agreement composed with
`beukers_apéry_rho_sub_sq_tendsto`, which records the real-axis value of
the even extension at the square-root point) -/
lemma beukersGExt_real_axis_tendsto (a : ℝ) (ha : 3 ≤ a) :
    Tendsto (fun u : ℝ => beukersGExt a ha (u : ℂ)) (𝓝[>] 0)
      (𝓝 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) := by
  have hreal := beukers_apéry_rho_sub_sq_tendsto a ha
  have hcomp : Tendsto (fun u : ℝ => ((beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) := by
    exact (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal
  refine Tendsto.congr' ?_ hcomp
  have hRpos : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  have hevlt : ∀ᶠ u : ℝ in 𝓝[>] 0, u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    have hIio : (Set.Iio (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) ∈ 𝓝 (0 : ℝ) := by
      have hm : (0 : ℝ) ∈ Set.Iio (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by simpa using hRpos
      exact isOpen_Iio.mem_nhds hm
    have hmem : (Set.Ioo (0 : ℝ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) ∈ 𝓝[>] (0 : ℝ) := by
      have hcore : (Set.Ioi (0 : ℝ)) ∩ (Set.Iio (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) ∈ 𝓝[>] (0 : ℝ) :=
        inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) hIio
      convert hcore using 1
      ext x
      simp [Set.Ioo, Set.Ioi, Set.Iio]
    have hmem' : {u : ℝ | u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))} ∈ 𝓝[>] (0 : ℝ) :=
      Filter.mem_of_superset hmem (by intro u hu; exact hu.2)
    exact hmem'
  filter_upwards [self_mem_nhdsWithin, hevlt] with u hu0' huR
  exact (beukersGExt_real_axis a ha hu0' huR).symm

/-- **two-sided boundary value of `G` at `u = 0`**:
`G(u) → ↑(−1/√(a²−1))` as `u → 0`, `u ≠ 0` (write `G = (HU(u)/u)·B(u)⁻¹`;
`HU(u)/u → HU′(0) = −2/B(0)` by differentiability of `HU` at `0`,
`B(u) → B(0) ≠ 0` by continuity, and the product is `−1/√(a²−1)` since
`B(0)² = 2√(a²−1)`) -/
lemma beukersGExt_tendsto_zero (a : ℝ) (ha : 3 ≤ a) :
    Tendsto (beukersGExt a ha) (𝓝[≠] (0 : ℂ)) (𝓝 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) := by
  have hRpos : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  have hub0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    have hn : ‖(0 : ℂ)‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by simpa using hRpos
    simpa [Metric.mem_ball, dist_zero_right] using hn
  have hd0 : deriv (beukersHU a ha) 0 = (-2) / beukersSqrtC a 0 := beukersHU_deriv a ha hub0
  have hdiff0 : DifferentiableAt ℂ (beukersHU a ha) 0 := beukersHU_differentiableAt a ha hub0
  have hd0' : HasDerivAt (beukersHU a ha) ((-2) / beukersSqrtC a 0) 0 := by
    simpa [hd0] using hdiff0.hasDerivAt
  have hslope := hd0'.tendsto_slope
  have hQuot : Tendsto (fun u : ℂ => beukersHU a ha u / u) (𝓝[≠] 0)
      (𝓝 ((-2) / beukersSqrtC a 0)) := hslope.congr' (by
    have hset : ({u : ℂ | u ≠ 0} : Set ℂ) ∈ 𝓝[≠] 0 := self_mem_nhdsWithin
    filter_upwards [hset] with u hu
    dsimp [slope]
    have h0 := beukersHU_zero a ha
    rw [h0]
    field_simp [hu]
    ring)
  have hBlim : Tendsto (fun u : ℂ => beukersSqrtC a u) (𝓝[≠] 0) (𝓝 (beukersSqrtC a 0)) :=
    (beukersSqrtC_continuousAt a ha (by simpa using hRpos)).tendsto.mono_left nhdsWithin_le_nhds
  have hB0ne : beukersSqrtC a 0 ≠ 0 := beukersSqrtC_zero_ne_zero a ha
  have hBinv : Tendsto (fun u : ℂ => (beukersSqrtC a u)⁻¹) (𝓝[≠] 0) (𝓝 (beukersSqrtC a 0)⁻¹) :=
    Tendsto.inv₀ hBlim hB0ne
  have hProd : Tendsto (fun u : ℂ => (beukersHU a ha u / u) * (beukersSqrtC a u)⁻¹)
      (𝓝[≠] 0) (𝓝 (((-2) / beukersSqrtC a 0) * (beukersSqrtC a 0)⁻¹)) := hQuot.mul hBinv
  have hval : ((-2) / beukersSqrtC a 0) * (beukersSqrtC a 0)⁻¹ = (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
    have hB0sq : (beukersSqrtC a 0) ^ 2 = (((2 * Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
      rw [beukersSqrtC_zero a]
      have hc0 : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) := by
        have : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
        positivity
      rw [← Complex.ofReal_pow]
      congr 1
      exact Real.sq_sqrt hc0
    field_simp [hB0ne]
    rw [hB0sq]
    have hs : Real.sqrt (a ^ 2 - 1) ≠ 0 := ne_of_gt (beukers_sqrt_sq_sub_one_pos a ha)
    have hnum : (-2 : ℂ) = (((-2 : ℝ) : ℂ)) := by norm_num
    rw [hnum]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hs]
  have hProd' : Tendsto (fun u : ℂ => (beukersHU a ha u / u) * (beukersSqrtC a u)⁻¹)
      (𝓝[≠] 0) (𝓝 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) := by
    rwa [hval] at hProd
  refine hProd'.congr' ?_
  have hball : (Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) ∈ 𝓝[≠] (0 : ℂ) := by
    have hball0 : Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 hRpos
    exact nhdsWithin_le_nhds hball0
  filter_upwards [self_mem_nhdsWithin, hball] with u hu hu_ball
  have huR : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    simpa [Metric.mem_ball, dist_zero_right] using hu_ball
  have hBne : beukersSqrtC a u ≠ 0 := by
    exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane (beukers_quad2c_mem_slitPlane a ha huR)
  dsimp [beukersGExt, beukersSigma]
  field_simp [hu, hBne]

/-- `G` is complex-differentiable at every `u ≠ 0` of the coordinate disc
(`G = HU/σ`, `HU` differentiable on the disc, `σ` differentiable and
`σ(u) = u·B(u) ≠ 0` for `u ≠ 0` in the disc) -/
lemma beukersGExt_differentiableAt (a : ℝ) (ha : 3 ≤ a) {u : ℂ} (hu0 : u ≠ 0)
    (huR : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    DifferentiableAt ℂ (beukersGExt a ha) u := by
  have hub : u ∈ Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
    simpa [Metric.mem_ball, dist_zero_right] using huR
  have hHU : DifferentiableAt ℂ (beukersHU a ha) u := beukersHU_differentiableAt a ha hub
  have hσ : DifferentiableAt ℂ (beukersSigma a) u := beukersSigma_differentiableAt a ha huR
  have hσne : beukersSigma a u ≠ 0 := by
    dsimp [beukersSigma]
    have hBne : beukersSqrtC a u ≠ 0 := by
      exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane (beukers_quad2c_mem_slitPlane a ha huR)
    exact mul_ne_zero hu0 hBne
  have hdiv : DifferentiableAt ℂ (fun w : ℂ => beukersHU a ha w / beukersSigma a w) u :=
    hHU.div hσ hσne
  exact hdiv


/-- the even holomorphic extension `G0 = G` redefined at `u = 0` with the
boundary value `−1/√(a²−1)` takes that value at `0` -/
lemma beukersGExt0_zero (a : ℝ) (ha : 3 ≤ a) :
    Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) 0 =
      (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
  exact Function.update_self 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) (beukersGExt a ha)

/-- the even holomorphic extension `G0` of `G` through `u = 0` is analytic at
`0` (removable singularity: `G` differentiable on the punctured disc,
`beukersGExt_tendsto_zero` gives continuity of the redefinition at `0`, via
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) -/
lemma beukersGExt0_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) :
    AnalyticAt ℂ (Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) 0 := by
  let L : ℂ := (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))
  have hRpos : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  have hball : (Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) ∈ 𝓝[≠] (0 : ℂ) := by
    have hball0 : Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 hRpos
    exact nhdsWithin_le_nhds hball0
  have hd : ∀ᶠ z in 𝓝[≠] 0, DifferentiableAt ℂ (Function.update (beukersGExt a ha) 0 L) z := by
    filter_upwards [hball, self_mem_nhdsWithin] with z hzball hz0
    have hzR : ‖z‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
      simpa [Metric.mem_ball, dist_zero_right] using hzball
    have hdG : DifferentiableAt ℂ (beukersGExt a ha) z := beukersGExt_differentiableAt a ha hz0 hzR
    have hEq : (Function.update (beukersGExt a ha) 0 L) =ᶠ[𝓝 z] (beukersGExt a ha) := by
      have hne_set : ({w : ℂ | w ≠ 0} : Set ℂ) ∈ 𝓝 z := isOpen_ne.mem_nhds hz0
      filter_upwards [hne_set] with w hw
      exact Function.update_of_ne hw L (beukersGExt a ha)
    exact hdG.congr_of_eventuallyEq hEq
  have hc : ContinuousAt (Function.update (beukersGExt a ha) 0 L) 0 := by
    exact continuousAt_update_same.mpr (by simpa [L] using beukersGExt_tendsto_zero a ha)
  simpa [L] using (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc)

/-- `G0` is even on the whole coordinate disc (even on the punctured disc by
`beukersGExt_neg`, and at `0` both sides equal the boundary value
`−1/√(a²−1)`); together with `beukersGExt0_analyticAt_zero` /
`beukersGExt0_differentiableOn` this is the **even holomorphic extension of
`A·(W−η_a)∘z(u)` through `u = 0`** with value `−1/√(a²−1)` (in the
`z`-plane: through the singularity `x = ρ`) -/
lemma beukersGExt0_even (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) (-u) =
      Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) u := by
  let L : ℂ := (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))
  by_cases hu0 : u = 0
  · subst u
    simp [Function.update]
  · have hum : ‖-u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by simpa using hub
    have hmu : -u ≠ 0 := by
      intro h
      apply hu0
      exact neg_eq_zero.mp h
    rw [Function.update_of_ne hmu L (beukersGExt a ha)]
    rw [Function.update_of_ne hu0 L (beukersGExt a ha)]
    exact beukersGExt_neg a ha hu0 hub

/-- the even holomorphic extension `G0` of `G` through `u = 0` is
complex-differentiable on the whole coordinate disc
(`beukersGExt0_analyticAt_zero` at `0`, `beukersGExt_differentiableAt` off
`0`) — the overconverged object of the `u`-coordinate -/
lemma beukersGExt0_differentiableOn (a : ℝ) (ha : 3 ≤ a) :
    DifferentiableOn ℂ (Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)))
      (Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact (beukersGExt0_analyticAt_zero a ha).differentiableAt.differentiableWithinAt
  · have huR : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hdG : DifferentiableAt ℂ (beukersGExt a ha) u := beukersGExt_differentiableAt a ha hu0 huR
    have hEq : (Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) =ᶠ[𝓝 u]
        (beukersGExt a ha) := by
      have hne_set : ({w : ℂ | w ≠ 0} : Set ℂ) ∈ 𝓝 u := isOpen_ne.mem_nhds hu0
      filter_upwards [hne_set] with w hw
      exact Function.update_of_ne hw (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) (beukersGExt a ha)
    exact (hdG.congr_of_eventuallyEq hEq).differentiableWithinAt


/-! ### G0 along the real axis and continuity (consolidation)

`G0 = G` redefined at `0` with the boundary value `−1/√(a²−1)` agrees with
`G` off `0` (definitionally, via `Function.update`), hence on the real axis
it equals `↑(A(ρ−u²)·(W(ρ−u²) − η_a))` for `0 < u` below the disc radius
(`beukersGExt0_real_axis`), and it is continuous on the whole coordinate
disc (from complex differentiability there, `beukersGExt0_continuousOn`),
in particular at `0` (`beukersGExt0_continuousAt_zero`). -/

/-- `G0` equals `G` away from `0` (definitional content of the update) -/
lemma beukersGExt0_eq_G {a : ℝ} {ha : 3 ≤ a} {u : ℂ} (hu : u ≠ 0) :
    Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) u =
      beukersGExt a ha u := by
  exact Function.update_of_ne hu (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) (beukersGExt a ha)

/-- `G0` agrees with the real-axis value of the companion product
`A·(W−η_a)` for real `0 < u < √(2c)`: `G0(↑u) = ↑(A(ρ−u²)·(W(ρ−u²)−η_a))` -/
lemma beukersGExt0_real_axis (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u)
    (huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) (u : ℂ) =
      ((beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) : ℝ) : ℂ) := by
  have hu0' : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu0)
  rw [beukersGExt0_eq_G hu0']
  exact beukersGExt_real_axis a ha hu0 huR

/-- the even holomorphic extension `G0` is continuous on the whole coordinate
disc (it is complex-differentiable there, `beukersGExt0_differentiableOn`) -/
lemma beukersGExt0_continuousOn (a : ℝ) (ha : 3 ≤ a) :
    ContinuousOn (Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)))
      (Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) := by
  exact (beukersGExt0_differentiableOn a ha).continuousOn

/-- `G0` is continuous at `0` (where its value is the boundary value
`−1/√(a²−1)`) -/
lemma beukersGExt0_continuousAt_zero (a : ℝ) (ha : 3 ≤ a) :
    ContinuousAt (Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))) 0 := by
  have hRpos : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  exact (beukersGExt0_continuousOn a ha).continuousAt (Metric.ball_mem_nhds 0 hRpos)


/-! ### G0 as a named function, and the descent through `u = 0` to `w = u²`

We package the even holomorphic extension
`G0 = G` redefined at `0` with the boundary value `−1/√(a²−1)` as the named
function `beukersG0` (bridge lemmas restate the `beukersGExt0_*` facts in
terms of it), and then apply the **even-analytic descent lemma**
(`Commons.Analysis.Analytic.even_analytic_factor_sq`: an analytic function
even near `0` factors through the square map) to obtain — brick **A4** of
the roadmap — a function `F` analytic at `0` (in the variable `w = u²`)
with `F (u²) = G0(u)` near `u = 0` and `F 0 = G0 0 = −1/√(a²−1)`.  The
real-axis consequence `beukersF_real_axis` records that, for small real
`t > 0`, `F (↑t) = ↑(A(ρ−t)·(W(ρ−t)−η_a))`, i.e. in the `x`-plane
(`x = ρ−t` below `ρ`) `F` is the analytic model of the companion product
`H(x) − η_a·A(x)` across the singularity `x = ρ` (`w = ρ−x`). -/

/-- the even holomorphic extension of `G` through `u = 0` with the boundary
value `−1/√(a²−1)` at `0` — the overconverged object of the `u`-coordinate -/
noncomputable def beukersG0 (a : ℝ) (ha : 3 ≤ a) : ℂ → ℂ :=
  Function.update (beukersGExt a ha) 0 (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ))

/-- `G0` is analytic at `0` (removable singularity, `beukersGExt0_analyticAt_zero`) -/
lemma beukersG0_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) : AnalyticAt ℂ (beukersG0 a ha) 0 := by
  simpa [beukersG0] using beukersGExt0_analyticAt_zero a ha

/-- `G0(0) = −1/√(a²−1)` (the boundary value) -/
lemma beukersG0_zero (a : ℝ) (ha : 3 ≤ a) :
    beukersG0 a ha 0 = (((-1 / Real.sqrt (a ^ 2 - 1) : ℝ) : ℂ)) := by
  simpa [beukersG0] using beukersGExt0_zero a ha

/-- `G0` equals `G` away from `0` -/
lemma beukersG0_eq_GExt (a : ℝ) (ha : 3 ≤ a) {u : ℂ} (hu : u ≠ 0) :
    beukersG0 a ha u = beukersGExt a ha u := by
  simpa [beukersG0] using beukersGExt0_eq_G hu

/-- `G0` is even on the whole coordinate disc -/
lemma beukersG0_even (a : ℝ) (ha : 3 ≤ a) {u : ℂ}
    (hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    beukersG0 a ha (-u) = beukersG0 a ha u := by
  simpa [beukersG0] using beukersGExt0_even a ha hub

/-- `G0` is complex-differentiable on the whole coordinate disc -/
lemma beukersG0_differentiableOn (a : ℝ) (ha : 3 ≤ a) :
    DifferentiableOn ℂ (beukersG0 a ha)
      (Metric.ball (0 : ℂ) (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)))) := by
  simpa [beukersG0] using beukersGExt0_differentiableOn a ha

/-- `G0` agrees with the real-axis value of the companion product for real
`0 < u < √(2c)` -/
lemma beukersG0_real_axis (a : ℝ) (ha : 3 ≤ a) {u : ℝ} (hu0 : 0 < u)
    (huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    beukersG0 a ha (u : ℂ) =
      ((beukersAReal a (beukersRho a - u ^ 2) *
        (beukersWReal a (beukersRho a - u ^ 2) - beukersEta a) : ℝ) : ℂ) := by
  simpa [beukersG0] using beukersGExt0_real_axis a ha hu0 huR

/-- evenness of `G0` on a whole neighborhood of `0` (input shape of the
even-analytic descent lemma) -/
lemma beukersG0_even_eventually (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ u in 𝓝 (0 : ℂ), beukersG0 a ha (-u) = beukersG0 a ha u := by
  have hRpos : 0 < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hRpos] with u hu
  have hub : ‖u‖ < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    simpa [Metric.mem_ball, dist_zero_right] using hu
  exact beukersG0_even a ha hub

/-- **brick A4 (existence)**: the even holomorphic `G0` descends through
`u = 0`: there is `F` analytic at `0` (in the variable `w = u²`) with
`F (u²) = G0(u)` for `u` near `0` and `F 0 = G0 0 = −1/√(a²−1)`.
(`Commons.Analysis.Analytic.even_analytic_factor_sq` applied to `G0`;
the quantitative radius version `even_analytic_factor_sq_onBall` is the
companion brick needed for the Cauchy bounds of the coefficient analysis.) -/
lemma beukersG0_descends_sq (a : ℝ) (ha : 3 ≤ a) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = beukersG0 a ha 0 ∧
      ∀ᶠ u in 𝓝 (0 : ℂ), F (u ^ 2) = beukersG0 a ha u := by
  exact Commons.Analysis.Analytic.even_analytic_factor_sq (f := beukersG0 a ha)
    (hf := beukersG0_analyticAt_zero a ha) (heven := beukersG0_even_eventually a ha)

/-- real-axis content of the descent: for a descended `F` (satisfying
`F (u²) = G0(u)` near `0`) there is `ε > 0` with `F (↑t) = ↑(A(ρ−t)·(W(ρ−t)−η_a))`
for all real `0 < t < ε` — in the `x`-plane (`x = ρ − t`, just below the
singularity `ρ`) the descended function extends the companion product
`H − η_a·A` across `x = ρ` -/
lemma beukersF_real_axis (a : ℝ) (ha : 3 ≤ a) {F : ℂ → ℂ}
    (hFeq : ∀ᶠ u in 𝓝 (0 : ℂ), F (u ^ 2) = beukersG0 a ha u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      F (t : ℂ) = ((beukersAReal a (beukersRho a - t) *
        (beukersWReal a (beukersRho a - t) - beukersEta a) : ℝ) : ℂ) := by
  classical
  let R : ℝ := Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))
  have hRpos : 0 < R := by
    dsimp [R]
    apply Real.sqrt_pos.2
    have hs : 0 < Real.sqrt (a ^ 2 - 1) := beukers_sqrt_sq_sub_one_pos a ha
    positivity
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → F (u ^ 2) = beukersG0 a ha u := by
    rw [Metric.eventually_nhds_iff] at hFeq
    rcases hFeq with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro u hu
    exact hδ (by simpa [dist_zero_right] using hu)
  let ε : ℝ := (min δ R) ^ 2
  refine ⟨ε, ?_, ?_⟩
  · have hmin : 0 < min δ R := lt_min hδ0 hRpos
    exact sq_pos_of_pos hmin
  · intro t ht0 htl
    have htε : t < ε := htl
    have hmin2 : min δ R > 0 := lt_min hδ0 hRpos
    have hsqrt_lt : Real.sqrt t < min δ R := by
      dsimp [ε] at htε
      exact (Real.sqrt_lt' hmin2).2 htε
    have hsqrt_lt_delta : Real.sqrt t < δ := lt_of_lt_of_le hsqrt_lt (min_le_left δ R)
    have hsqrt_lt_R : Real.sqrt t < R := lt_of_lt_of_le hsqrt_lt (min_le_right δ R)
    have hu0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have huR : Real.sqrt t < R := hsqrt_lt_R
    have hval : F (((Real.sqrt t : ℂ) ^ 2)) = beukersG0 a ha (Real.sqrt t : ℂ) := by
      have hub : ‖(Real.sqrt t : ℂ)‖ < δ := by
        have hx : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
        simpa [RCLike.norm_ofReal (K := ℂ), abs_of_nonneg hx] using hsqrt_lt_delta
      exact hδ (Real.sqrt t : ℂ) (by simpa [dist_zero_right] using hub)
    have hsq : (((Real.sqrt t : ℂ) ^ 2)) = (t : ℂ) := by
      rw [← Complex.ofReal_pow]
      congr 1
      exact Real.sq_sqrt (le_of_lt ht0)
    have hG : beukersG0 a ha (Real.sqrt t : ℂ) =
        ((beukersAReal a (beukersRho a - t) *
          (beukersWReal a (beukersRho a - t) - beukersEta a) : ℝ) : ℂ) := by
      have h1 := beukersG0_real_axis a ha hu0 huR
      have hu2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht0)
      simpa [hu2] using h1
    simpa [hsq] using hval.trans hG


/-- **brick A4 (ball form)**: for every `R0` below the radius
`R_u = √(2·√(a²−1))` of the `u`-coordinate disc, the even holomorphic `G0`
descends to `F` with a power series on the `w = u²`-disc of radius `R0²`
(`HasFPowerSeriesOnBall F q 0 (↑R0)²`), `F 0 = G0 0 = −1/√(a²−1)`, and
`F (u²) = G0(u)` for **every** `‖u‖ < R0`.  (Quantitative version of
`beukersG0_descends_sq`, via
`Commons.Analysis.Analytic.even_analytic_factor_sq_onBall`, fed with the
closed-ball power series of `G0` obtained from
`DifferentiableOn.hasFPowerSeriesOnBall`; this is the radius control that the
Cauchy-coefficient analysis of the continuation needs.) -/
lemma beukersG0_descends_sq_onBall (a : ℝ) (ha : 3 ≤ a) (R0 : ℝ≥0) (hR0 : 0 < R0)
    (hR0lt : (R0 : ℝ) < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) :
    ∃ F : ℂ → ℂ, ∃ q : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2)) ∧
        F 0 = beukersG0 a ha 0 ∧
        ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z := by
  classical
  let f : ℂ → ℂ := beukersG0 a ha
  let Ru : ℝ := Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))
  have hR0pos_r : (0 : ℝ) < (R0 : ℝ) := by exact_mod_cast hR0
  have hR0lt_r : (R0 : ℝ) < Ru := by simpa [Ru] using hR0lt
  have hd_open : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) Ru) := by
    simpa [f, Ru] using beukersG0_differentiableOn a ha
  have hcl : Metric.closedBall (0 : ℂ) (R0 : ℝ) ⊆ Metric.ball (0 : ℂ) Ru :=
    Metric.closedBall_subset_ball hR0lt_r
  have hd_cl : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R0 : ℝ)) := hd_open.mono hcl
  have hfs : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R0) 0 ((R0 : ℝ≥0∞)) :=
    hd_cl.hasFPowerSeriesOnBall hR0
  have heven : ∀ z : ℂ, z ∈ Metric.eball (0 : ℂ) ((R0 : ℝ≥0∞)) → f (-z) = f z := by
    intro z hz
    have hzn : ‖z‖ < (R0 : ℝ) := by
      rw [mem_eball_zero_iff] at hz
      exact_mod_cast hz
    have hub : ‖z‖ < Ru := lt_trans hzn hR0lt_r
    exact beukersG0_even a ha hub
  rcases (Commons.Analysis.Analytic.even_analytic_factor_sq_onBall
    (f := f) (p := cauchyPowerSeries f 0 R0) (R := (R0 : ℝ≥0∞)) hfs heven) with ⟨F, q, hF, hF0, hFeq⟩
  refine ⟨F, q, hF, hF0, ?_⟩
  intro z hz
  have hzeb : z ∈ Metric.eball (0 : ℂ) ((R0 : ℝ≥0∞)) := by
    rw [mem_eball_zero_iff]
    exact_mod_cast hz
  exact hFeq z hzeb


/-! ### Elementary radius inequalities for the coefficient analysis (A6)

The continuation of `H(x) − η_a·A(x)` through the singularity `x = ρ` has
the `w = u²`-coordinate disc of radius `R_w = 2·√(a²−1)` (`R_w = R_u²`,
`R_u = √(2·√(a²−1))` the `u`-disc radius of `G0`).  For the Cauchy
coefficient bounds at `x = 0` one needs a circle `|x| = r` with
`1/a < r` inside that disc, i.e. `ρ + 1/a < 2·√(a²−1)`.  The next two
lemmas give the elementary real inequality behind that choice for `a ≥ 3`
(proof: `√(a²−1) = a·√(1−1/a²)`, and
`3√(1−1/a²) − 1 ≥ 3·√(8/9) − 1 = 2√2 − 1 > 0`...). -/

/-- `2√(a²−1) − ρ_a > 1/a` for `a ≥ 3` (equivalently `ρ_a + 1/a < 2√(a²−1)`):
the `u`-disc radius `R_u² = 2√(a²−1)` of the continuation leaves room for a
Cauchy circle at `x = 0` of radius bigger than `1/a` -/
lemma beukers_cont_radius_gt_one_div (a : ℝ) (ha : 3 ≤ a) :
    (1 : ℝ) / a < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by
  -- √(a²−1) ≥ a−1 for a ≥ 1 (square both sides), so
  -- 2√(a²−1) − ρ_a = 3√(a²−1) − a ≥ 3(a−1) − a = 2a−3 ≥ 3 > 1/a
  have hpos : 0 < a := by linarith
  -- strict `√(a²−1) > a−1` (square both sides; a > 1)
  have hLstrict : a - 1 < Real.sqrt (a ^ 2 - 1) := by
    have hsq_lt : (a - 1) ^ 2 < a ^ 2 - 1 := by nlinarith
    have hsqrt_lt : Real.sqrt ((a - 1) ^ 2) < Real.sqrt (a ^ 2 - 1) :=
      Real.sqrt_lt_sqrt (sq_nonneg (a - 1)) hsq_lt
    have hroot : Real.sqrt ((a - 1) ^ 2) = a - 1 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      linarith
    rwa [hroot] at hsqrt_lt
  -- 3·√(a²−1) − a = (2a−6) + 3·(√(a²−1) − (a−1)) + 3 > 3
  have hlow : 3 < 3 * Real.sqrt (a ^ 2 - 1) - a := by
    have hd : 0 < Real.sqrt (a ^ 2 - 1) - (a - 1) := sub_pos.mpr hLstrict
    have hpos3 : 0 < 3 * (Real.sqrt (a ^ 2 - 1) - (a - 1)) := mul_pos (by norm_num) hd
    have hnonneg : 0 ≤ 2 * a - 6 := by nlinarith
    have hsum : 0 < (2 * a - 6) + 3 * (Real.sqrt (a ^ 2 - 1) - (a - 1)) :=
      add_pos_of_nonneg_of_pos hnonneg hpos3
    have htotal : 3 * Real.sqrt (a ^ 2 - 1) - a =
        (2 * a - 6) + 3 * (Real.sqrt (a ^ 2 - 1) - (a - 1)) + 3 := by ring
    rw [htotal]
    nlinarith
  have hgt : (1 : ℝ) / a < 3 := (div_lt_iff₀ hpos).2 (by nlinarith)
  have hmain : (1 : ℝ) / a < 3 * Real.sqrt (a ^ 2 - 1) - a :=
    lt_trans hgt hlow
  have hrho : 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a =
      3 * Real.sqrt (a ^ 2 - 1) - a := by
    dsimp [beukersRho]
    ring
  rwa [hrho]

/-- `ρ_a + 1/a < 2√(a²−1)` for `a ≥ 3` (arithmetic rearrangement of
`beukers_cont_radius_gt_one_div`) -/
lemma beukers_rho_add_one_div_lt_two_sqrt (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a + (1 : ℝ) / a < 2 * Real.sqrt (a ^ 2 - 1) := by
  linarith [beukers_cont_radius_gt_one_div a ha]


/-! ### Analyticity at `0` of the complex lifts and of the real companion
functions (A5, stage 1)

The coefficient bridge (A5) needs the real companion functions
`A(a,x) = 1/√Q(x)` and `W(a,x)` to be **real-analytic at `0`**.  These are
restrictions to the real axis of the complex lifts `Aℂ`, `Wℂ`
(`beukersAComplex`, `beukersWComplex`) which are holomorphic at `0` because
`Q(0) = 1` lies in the slit plane where `Complex.sqrt`/`Complex.log` are
holomorphic.  This section proves that holomorphy
(`beukersAComplex_analyticAt_zero`, `beukersWComplex_analyticAt_zero`, using
`Commons.Analysis.Complex.sqrt_analyticAt` and Mathlib's
`analyticAt_clog`), the values `Aℂ(0) = 1` (`beukersAComplex_zero`), and —
via `AnalyticAt.re_ofReal` together with the real-axis agreements
`beukersAComplex_eq_ofReal`/`beukersWComplex_eq_ofReal` — the real
analyticity **`beukersAReal_analyticAt_zero`**, **`beukersWReal_analyticAt_zero`**.
(The identification of their real power-series coefficients at `0` with the
formal coefficients `u_n`, `v_n` is the next stage of A5.) -/

/-- `Q(0) = 1` -/
lemma beukersQuadC_zero (a : ℝ) : beukersQuadC a 0 = 1 := by
  simp [beukersQuadC]

/-- `Aℂ(0) = 1` -/
lemma beukersAComplex_zero (a : ℝ) : beukersAComplex a 0 = 1 := by
  dsimp [beukersAComplex]
  rw [beukersQuadC_zero]
  simp

/-- the quadratic `Q` is holomorphic at `0` (it is a polynomial) -/
lemma beukersQuadC_analyticAt_zero (a : ℝ) : AnalyticAt ℂ (fun z : ℂ => beukersQuadC a z) 0 := by
  have hQ : AnalyticAt ℂ (fun z : ℂ => 1 - 2 * (a : ℂ) * z + z ^ 2) 0 := by
    fun_prop
  simpa [beukersQuadC] using hQ

/-- `Aℂ = 1/√Q` is holomorphic at `0` (`Q(0) = 1 ∈ slitPlane`, `√` is
holomorphic on the slit plane, inverse of the nonzero value `1`) -/
lemma beukersAComplex_analyticAt_zero (a : ℝ) : AnalyticAt ℂ (beukersAComplex a) 0 := by
  have hQ' : AnalyticAt ℂ (fun z : ℂ => beukersQuadC a z) 0 := beukersQuadC_analyticAt_zero a
  have hslit : beukersQuadC a 0 ∈ Complex.slitPlane := by
    rw [beukersQuadC_zero]
    exact Complex.one_mem_slitPlane
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (beukersQuadC a z)) 0 := by
    exact (Commons.Analysis.Complex.sqrt_analyticAt (z := beukersQuadC a 0) hslit).comp hQ'
  have hsqrt0ne : Complex.sqrt (beukersQuadC a 0) ≠ 0 := by
    exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane hslit
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Complex.sqrt (beukersQuadC a z))⁻¹) 0 :=
    hs.inv hsqrt0ne
  change AnalyticAt ℂ (fun z : ℂ => (Complex.sqrt (beukersQuadC a z))⁻¹) 0
  exact hinv

/-- the value at `0` of the denominator `a − z + √Q(z)` of the log argument
of `Wℂ` is `a+1` -/
lemma beukersWComplex_denom_zero (a : ℝ) :
    (a : ℂ) - 0 + Complex.sqrt (beukersQuadC a 0) = (((a + 1 : ℝ) : ℂ)) := by
  rw [beukersQuadC_zero]
  simp

/-- the log argument of `Wℂ` takes the value `1` at `0`, hence lies in the
slit plane there -/
lemma beukersWComplex_arg_zero (a : ℝ) (ha : 3 ≤ a) :
    (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - 0 + Complex.sqrt (beukersQuadC a 0))) = 1 := by
  rw [beukersWComplex_denom_zero a]
  have h : (a + 1 : ℝ) ≠ 0 := by linarith
  have hc : (((a + 1 : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast h
  field_simp [hc]

/-- `Wℂ = log((a+1)/(a−z+√Q(z)))` is holomorphic at `0` (log argument is
holomorphic with value `1` at `0`, `log` holomorphic on the slit plane) -/
lemma beukersWComplex_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) :
    AnalyticAt ℂ (beukersWComplex a) 0 := by
  have hQ' : AnalyticAt ℂ (fun z : ℂ => beukersQuadC a z) 0 := beukersQuadC_analyticAt_zero a
  have hslit : beukersQuadC a 0 ∈ Complex.slitPlane := by
    rw [beukersQuadC_zero]
    exact Complex.one_mem_slitPlane
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (beukersQuadC a z)) 0 := by
    exact (Commons.Analysis.Complex.sqrt_analyticAt (z := beukersQuadC a 0) hslit).comp hQ'
  have hid : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) - z) 0 := by
    fun_prop
  have hden : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) 0 :=
    hid.add hs
  have hden0_ne : (a : ℂ) - 0 + Complex.sqrt (beukersQuadC a 0) ≠ 0 := by
    rw [beukersWComplex_denom_zero a]
    have h : (a + 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast h
  have hnum : AnalyticAt ℂ (fun z : ℂ => (((a + 1 : ℝ) : ℂ))) 0 := by
    fun_prop
  have hratio : AnalyticAt ℂ
      (fun z : ℂ => (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)))) 0 :=
    hnum.div hden hden0_ne
  have harg0 : ((((a + 1 : ℝ) : ℂ) /
      ((a : ℂ) - 0 + Complex.sqrt (beukersQuadC a 0)))) ∈ Complex.slitPlane := by
    rw [beukersWComplex_arg_zero a ha]
    exact Complex.one_mem_slitPlane
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => Complex.log
        ((((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z))))) 0 :=
    AnalyticAt.clog hratio harg0
  change AnalyticAt ℂ
    (fun z : ℂ => Complex.log
      ((((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z))))) 0
  exact hlog

/-- the real companion `A(a,x) = 1/√Q(x)` is real-analytic at `0` (it is the
real part of the holomorphic `Aℂ` on the real axis) -/
lemma beukersAReal_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) : AnalyticAt ℝ (beukersAReal a) 0 := by
  have hre : AnalyticAt ℝ (fun x : ℝ => (beukersAComplex a (x : ℂ)).re) 0 :=
    AnalyticAt.re_ofReal (beukersAComplex_analyticAt_zero a)
  apply hre.congr
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  filter_upwards [hset] with x hx
  have hval := beukersAComplex_eq_ofReal a ha hx
  calc
    (beukersAComplex a (x : ℂ)).re = ((beukersAReal a x : ℂ)).re := by rw [hval]
    _ = beukersAReal a x := by simp

/-- the real companion antiderivative `W(a,x)` is real-analytic at `0` (it is
the real part of the holomorphic `Wℂ` on the real axis) -/
lemma beukersWReal_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) : AnalyticAt ℝ (beukersWReal a) 0 := by
  have hre : AnalyticAt ℝ (fun x : ℝ => (beukersWComplex a (x : ℂ)).re) 0 :=
    AnalyticAt.re_ofReal (beukersWComplex_analyticAt_zero a ha)
  apply hre.congr
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  filter_upwards [hset] with x hx
  have hval := beukersWComplex_eq_ofReal a ha hx
  calc
    (beukersWComplex a (x : ℂ)).re = ((beukersWReal a x : ℂ)).re := by rw [hval]
    _ = beukersWReal a x := by simp


/-! ### A5 stage 2 — the coefficient bridge: `A(a,x) = Σ u_n(a)·xⁿ` and `W = Σ v`-type
coefficients near `0` (real axis)

The analytic coefficient machinery.  `A(a,x) = 1/√(1−2ax+x²)` is the real
analytic function of the module (real-analytic at `0`,
`beukersAReal_analyticAt_zero`); this section proves:

* the **first-order ODE** for the real companion
  `beukersAReal_hasDerivAt`: `A′ = (a−x)·A/Q` on `(−∞, ρ)` (from the closed
  form through the `√`), and its `𝓝 0` version
  `beukersAReal_ode_eventually`;
* the **3-term recurrence** for the iterated derivatives at `0`
  (`beukersAReal_iterDeriv_step_all`), obtained by differentiating the ODE
  `m` times at `0` and expanding with the Leibniz rule
  (`iteratedDeriv_quadratic_mul_zero`, a general quadratic-product formula,
  with the auxiliary polynomial/choose/sum lemmas);
* the real coefficient sequence `beukersUR a : ℕ → ℝ` (mirror of
  `beukersU`) and its identification with the rational one
  (`beukersUR_eq_cast`);
* **the coefficient bridge** `beukersAReal_iterDeriv_eq_fact`:
  `A^{(n)}(0) = n!·u_n(a)` — hence (via `AnalyticAt.hasFPowerSeriesAt` and
  `hasFPowerSeriesAt_iff`) the analytic identity
  `beukersAReal_hasSum_series`: near `0`,
  `A(a,x) = Σₙ u_n(a)·xⁿ` (pointwise `HasSum`);
* the **W-side**: `W′ = A` gives `beukersWReal_iterDeriv_succ` /
  `beukersWReal_iterDeriv_eq` (`W^{(n)}(0) = n!·wₙ`, `w₀ = 0`,
  `wₙ = u_{n−1}/n`) and the analytic identity
  `beukersWReal_hasSum_series` near `0`.

The `H = A·W` coefficient half (`beukersH_hasSum_series`,
`beukers_hasSum_apéry_series`, with the real companion coefficients
`beukersVR` equal to the cast of the rational `beukersV`) is committed in the
next section; the complex-lift identification is **DONE in the A5
stage-2 sections below** (`beukersAComplex_coeff_eq`,
`beukersWComplex_coeff_eq`: the Taylor coefficients of `Aℂ`, `Wℂ` at `0`
equal `u_n(a)`, `wₙ(a)`).
-/

lemma iteratedDeriv_quadratic_poly_zero (p0 p1 p2 : ℝ) (i : ℕ) :
    iteratedDeriv i (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) 0 =
      if i = 0 then p0 else if i = 1 then p1 else if i = 2 then (2 : ℝ) * p2 else 0 := by
  have hA : iteratedDeriv i (fun x : ℝ => p0) 0 = if i = 0 then p0 else 0 := by
    rw [iteratedDeriv_const]
  have hB : iteratedDeriv i (fun x : ℝ => p1 * x) 0 = if i = 1 then p1 else 0 := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_fun_id_zero]
    by_cases hi : i = 1 <;> simp [hi]
  have hC : iteratedDeriv i (fun x : ℝ => p2 * x ^ 2) 0 = if i = 2 then (2 : ℝ) * p2 else 0 := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_fun_pow_zero]
    by_cases hi2 : i = 2
    · subst i; simp; ring
    · simp [hi2]
  have hdec : (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) =
      ((fun x : ℝ => p0) + (fun x : ℝ => p1 * x)) + (fun x : ℝ => p2 * x ^ 2) := by
    funext x
    simp only [Pi.add_apply]
  rw [hdec]
  have hc0 : ContDiffAt ℝ i (fun x : ℝ => p0) 0 := by fun_prop
  have hc1 : ContDiffAt ℝ i (fun x : ℝ => p1 * x) 0 := by fun_prop
  have hc2 : ContDiffAt ℝ i (fun x : ℝ => p2 * x ^ 2) 0 := by fun_prop
  have hc01 : ContDiffAt ℝ i ((fun x : ℝ => p0) + (fun x : ℝ => p1 * x)) 0 := hc0.add hc1
  have h012 := iteratedDeriv_add hc01 hc2
  have h01 := iteratedDeriv_add hc0 hc1
  rw [h012, h01]
  rw [hA, hB, hC]
  by_cases h0 : i = 0
  · subst i; simp
  · by_cases h1 : i = 1
    · subst i; simp
    · by_cases h2 : i = 2
      · subst i; simp
      · simp [h0, h1, h2]

lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have hc1 : m.choose 1 = m := by exact Nat.choose_one_right m
    have hsub : (m + 1) - 1 = m := by simp
    rw [hc1, hsub]
    have hdist : 2 * (m + m.choose 2) = 2 * m + 2 * m.choose 2 := by omega
    rw [hdist]
    rw [ih]
    cases m with
    | zero => simp
    | succ k =>
      have hkm : Nat.succ k - 1 = k := by simp
      rw [hkm]
      ring

lemma sum_ite_range_of_le (m a : ℕ) (ha : a ≤ m) (c : ℝ) :
    (∑ i ∈ Finset.range (m + 1), (if i = a then c else 0)) = c := by
  have hin : a ∈ Finset.range (m + 1) := by
    have : a < m + 1 := Nat.lt_succ_of_le ha
    simpa [Finset.mem_range]
  have h0 : ∀ b ∈ Finset.range (m + 1), b ≠ a → (if b = a then c else 0) = 0 := by
    intro b hb hbne
    simp [hbne]
  have h1 : a ∉ Finset.range (m + 1) → (if a = a then c else 0) = 0 := by
    intro h
    exfalso
    exact h hin
  simpa using (Finset.sum_eq_single (a := a) (s := Finset.range (m + 1))
    (f := fun i : ℕ => if i = a then c else 0) h0 h1)

lemma iteratedDeriv_quadratic_mul_zero (m : ℕ) (hm : 2 ≤ m) {g : ℝ → ℝ}
    (hg : ContDiffAt ℝ m g 0) (p0 p1 p2 : ℝ) :
    iteratedDeriv m (fun x : ℝ => (p0 + p1 * x + p2 * x ^ 2) * g x) 0 =
      p0 * iteratedDeriv m g 0 +
      (m : ℝ) * p1 * iteratedDeriv (m - 1) g 0 +
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * iteratedDeriv (m - 2) g 0 := by
  have hP : ContDiffAt ℝ m (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) 0 := by fun_prop
  have hleib := iteratedDeriv_mul (𝕜 := ℝ) (x := (0 : ℝ)) (n := m)
    (f := fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) (g := g) hP hg
  change iteratedDeriv m ((fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) * g) 0 =
    p0 * iteratedDeriv m g 0 + (m : ℝ) * p1 * iteratedDeriv (m - 1) g 0 +
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * iteratedDeriv (m - 2) g 0
  rw [hleib]
  let e : ℕ → ℝ := fun k => iteratedDeriv k g 0
  have hPderiv : ∀ i : ℕ, iteratedDeriv i (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) 0 =
      if i = 0 then p0 else if i = 1 then p1 else if i = 2 then (2 : ℝ) * p2 else 0 := by
    intro i
    exact iteratedDeriv_quadratic_poly_zero p0 p1 p2 i
  let A0 : ℝ := (m.choose 0 : ℝ) * p0 * e m
  let A1 : ℝ := (m.choose 1 : ℝ) * p1 * e (m - 1)
  let A2 : ℝ := (m.choose 2 : ℝ) * ((2 : ℝ) * p2) * e (m - 2)
  have hterm : ∀ i : ℕ,
      (m.choose i : ℝ) * iteratedDeriv i (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) 0 * e (m - i) =
        (if i = 0 then A0 else 0) + (if i = 1 then A1 else 0) + (if i = 2 then A2 else 0) := by
    intro i
    rw [hPderiv i]
    by_cases h0 : i = 0
    · subst i; simp [A0, A1, A2]
    · by_cases h1 : i = 1
      · subst i; simp [A0, A1, A2]
      · by_cases h2 : i = 2
        · subst i; simp [A0, A1, A2]
        · simp [h0, h1, h2, A0, A1, A2]
  calc
    (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        iteratedDeriv i (fun x : ℝ => p0 + p1 * x + p2 * x ^ 2) 0 * e (m - i))
      = (∑ i ∈ Finset.range (m + 1),
          ((if i = 0 then A0 else 0) + (if i = 1 then A1 else 0) + (if i = 2 then A2 else 0))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = (∑ i ∈ Finset.range (m + 1), (if i = 0 then A0 else 0)) +
        (∑ i ∈ Finset.range (m + 1), (if i = 1 then A1 else 0)) +
        (∑ i ∈ Finset.range (m + 1), (if i = 2 then A2 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = A0 + A1 + A2 := by
          rw [sum_ite_range_of_le m 0 (by omega) A0]
          rw [sum_ite_range_of_le m 1 (by omega) A1]
          rw [sum_ite_range_of_le m 2 (by omega) A2]
    _ = p0 * e m + (m : ℝ) * p1 * e (m - 1) +
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * e (m - 2) := by
          have hc0 : (m.choose 0 : ℝ) = 1 := by simp [Nat.choose_zero_right]
          have hc1 : (m.choose 1 : ℝ) = (m : ℝ) := by simp [Nat.choose_one_right]
          have hc2 : (m.choose 2 : ℝ) * (2 : ℝ) = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
            have hnat := two_mul_choose_two m
            have hcast : ((2 * m.choose 2 : ℕ) : ℝ) = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
              rw [hnat]
              rw [Nat.cast_mul]
            have hmul : (m.choose 2 : ℝ) * (2 : ℝ) = ((2 * m.choose 2 : ℕ) : ℝ) := by
              rw [Nat.cast_mul]
              ring
            rw [hmul]
            exact hcast
          dsimp [A0, A1, A2]
          rw [hc0, hc1]
          have hA2eq : (m.choose 2 : ℝ) * ((2 : ℝ) * p2) * e (m - 2) =
              ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * e (m - 2) := by
            calc
              (m.choose 2 : ℝ) * ((2 : ℝ) * p2) * e (m - 2) =
                  ((m.choose 2 : ℝ) * (2 : ℝ)) * p2 * e (m - 2) := by ring
              _ = ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * e (m - 2) := by rw [hc2]
          rw [hA2eq]
          simpa
    _ = p0 * iteratedDeriv m g 0 + (m : ℝ) * p1 * iteratedDeriv (m - 1) g 0 +
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * p2 * iteratedDeriv (m - 2) g 0 := by
          simp [e]

-- ============ Beukers-specific: AReal derivative + ODE + recurrence ============

lemma beukersAReal_hasDerivAt (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    HasDerivAt (beukersAReal a) ((a - x) * beukersAReal a x / beukersQuad a x) x := by
  have hQpos : 0 < beukersQuad a x := beukersQuad_pos_of_lt_rho a x ha hxρ
  have hQne : beukersQuad a x ≠ 0 := ne_of_gt hQpos
  have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (beukersQuad a t))
      ((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a)) x :=
    beukers_sqrtQ_raw_hasDerivAt a x hQne
  have hinv : HasDerivAt (fun t : ℝ => (Real.sqrt (beukersQuad a t))⁻¹)
      (-(((1 / (2 * Real.sqrt (beukersQuad a x))) * (2 * x - 2 * a))) /
        (Real.sqrt (beukersQuad a x)) ^ 2) x := hsq.inv (ne_of_gt (Real.sqrt_pos.2 hQpos))
  have hsqQ : (Real.sqrt (beukersQuad a x)) ^ 2 = beukersQuad a x := Real.sq_sqrt (le_of_lt hQpos)
  change HasDerivAt (fun t : ℝ => (Real.sqrt (beukersQuad a t))⁻¹)
    ((a - x) * (Real.sqrt (beukersQuad a x))⁻¹ / beukersQuad a x) x
  convert hinv using 1
  rw [hsqQ]
  field_simp [hQne]
  ring

lemma beukersAReal_ode_eventually (a : ℝ) (ha : 3 ≤ a) :
    (fun x : ℝ => beukersQuad a x * deriv (beukersAReal a) x) =ᶠ[𝓝 (0 : ℝ)]
      fun x : ℝ => (a - x) * beukersAReal a x := by
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  filter_upwards [hset] with x hx
  have hd := beukersAReal_hasDerivAt a ha hx
  have hder : deriv (beukersAReal a) x = (a - x) * beukersAReal a x / beukersQuad a x := hd.deriv
  rw [hder]
  field_simp [ne_of_gt (beukersQuad_pos_of_lt_rho a x ha hx)]

lemma beukersAReal_deriv_contDiff (a : ℝ) (ha : 3 ≤ a) (m : ℕ) :
    ContDiffAt ℝ m (deriv (beukersAReal a)) 0 := by
  have hf : ContDiffAt ℝ (m + 1) (beukersAReal a) 0 :=
    (beukersAReal_analyticAt_zero a ha).contDiffAt (n := (m + 1 : ℕ))
  exact ContDiffAt.derivWithin (𝕜 := ℝ) (x := (0 : ℝ)) (m := m) (n := (m + 1 : ℕ)) hf (by rfl)

lemma beukersAReal_contDiff (a : ℝ) (ha : 3 ≤ a) (m : ℕ) :
    ContDiffAt ℝ m (beukersAReal a) 0 := by
  exact (beukersAReal_analyticAt_zero a ha).contDiffAt (n := m)

-- main recurrence for m >= 2, expressed via iteratedDeriv of f
lemma beukersAReal_iterDeriv_step (a : ℝ) (ha : 3 ≤ a) (m : ℕ) (hm : 2 ≤ m) :
    iteratedDeriv (m + 1) (beukersAReal a) 0 =
      a * ((2 * (m : ℝ)) + 1) * iteratedDeriv m (beukersAReal a) 0 -
        ((m : ℝ) ^ 2) * iteratedDeriv (m - 1) (beukersAReal a) 0 := by
  let f : ℝ → ℝ := beukersAReal a
  let e : ℕ → ℝ := fun k => iteratedDeriv k f 0
  have hodd : ∀ k : ℕ, iteratedDeriv k (fun x : ℝ => beukersQuad a x * deriv f x) 0 =
      iteratedDeriv k (fun x : ℝ => (a - x) * f x) 0 := by
    intro k
    have heq := beukersAReal_ode_eventually a ha
    have heq' : (fun x : ℝ => beukersQuad a x * deriv (beukersAReal a) x) =ᶠ[𝓝 (0 : ℝ)]
        fun x : ℝ => (a - x) * beukersAReal a x := heq
    simpa [f] using (Filter.EventuallyEq.iteratedDeriv_eq k heq')
  have hsub : ∀ k : ℕ, iteratedDeriv k (deriv f) 0 = e (k + 1) := by
    intro k
    rw [← iteratedDeriv_succ']
  -- expand the left side at order m with Q = 1 - 2aX + X^2
  have hL : iteratedDeriv m (fun x : ℝ => beukersQuad a x * deriv f x) 0 =
      e (m + 1) + (m : ℝ) * (-2 * a) * e m +
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * e (m - 1) := by
    have h1 := iteratedDeriv_quadratic_mul_zero m hm (beukersAReal_deriv_contDiff a ha m) 1 (-2 * a) 1
    calc
      iteratedDeriv m (fun x : ℝ => beukersQuad a x * deriv f x) 0
          = iteratedDeriv m (fun x : ℝ => (1 + (-2 * a) * x + 1 * x ^ 2) * deriv f x) 0 := by
              apply congrArg (fun g : ℝ → ℝ => iteratedDeriv m g 0)
              funext x
              unfold beukersQuad
              ring_nf
      _ = 1 * iteratedDeriv m (deriv f) 0 + (m : ℝ) * (-2 * a) * iteratedDeriv (m - 1) (deriv f) 0 +
          ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * 1 * iteratedDeriv (m - 2) (deriv f) 0 := by
              simpa using h1
      _ = iteratedDeriv m (deriv f) 0 + (m : ℝ) * (-2 * a) * iteratedDeriv (m - 1) (deriv f) 0 +
          ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * iteratedDeriv (m - 2) (deriv f) 0 := by ring
      _ = e (m + 1) + (m : ℝ) * (-2 * a) * e m +
          ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * e (m - 1) := by
              have hm2 : 2 ≤ m := hm
              have h1r : (m - 1) + 1 = m := by omega
              have h2r : (m - 2) + 1 = m - 1 := by omega
              rw [hsub m]
              rw [hsub (m - 1), h1r]
              rw [hsub (m - 2), h2r]
  have hR : iteratedDeriv m (fun x : ℝ => (a - x) * f x) 0 =
      a * e m - (m : ℝ) * e (m - 1) := by
    have h2 := iteratedDeriv_quadratic_mul_zero m hm (beukersAReal_contDiff a ha m) a (-1) 0
    calc
      iteratedDeriv m (fun x : ℝ => (a - x) * f x) 0
          = iteratedDeriv m (fun x : ℝ => (a + (-1) * x + 0 * x ^ 2) * f x) 0 := by
              apply congrArg (fun g : ℝ → ℝ => iteratedDeriv m g 0)
              funext x
              ring_nf
      _ = a * iteratedDeriv m f 0 + (m : ℝ) * (-1) * iteratedDeriv (m - 1) f 0 +
          ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) * 0 * iteratedDeriv (m - 2) f 0 := by
              simpa using h2
      _ = a * e m - (m : ℝ) * e (m - 1) := by
              dsimp [e]
              ring
  have heq_m := hodd m
  rw [hL, hR] at heq_m
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ m)]
    norm_num
  rw [hcast] at heq_m
  have hfinal : e (m + 1) = a * ((2 * (m : ℝ)) + 1) * e m - ((m : ℝ) ^ 2) * e (m - 1) := by
    nlinarith [heq_m]
  simpa [e, f] using hfinal


-- ============ base values and e2 ============

lemma beukersAReal_zero_value (a : ℝ) : beukersAReal a 0 = 1 := by
  dsimp [beukersAReal, beukersSqrtQ, beukersQuad]
  norm_num

lemma beukersAReal_deriv_zero (a : ℝ) (ha : 3 ≤ a) : deriv (beukersAReal a) 0 = a := by
  have h0ρ : (0 : ℝ) < beukersRho a := beukers_rho_pos a ha
  have hd := beukersAReal_hasDerivAt a ha h0ρ
  -- hd : HasDerivAt (beukersAReal a) ((a - 0) * beukersAReal a 0 / beukersQuad a 0) 0
  have hval : (a - 0) * beukersAReal a 0 / beukersQuad a 0 = a := by
    rw [beukersAReal_zero_value]
    dsimp [beukersQuad]
    norm_num
  rw [hval] at hd
  exact hd.deriv

lemma beukersAReal_iterDeriv_two (a : ℝ) (ha : 3 ≤ a) :
    iteratedDeriv 2 (beukersAReal a) 0 = 3 * a ^ 2 - 1 := by
  have h0ρ : (0 : ℝ) < beukersRho a := beukers_rho_pos a ha
  -- deriv f agrees with g := fun x => (a-x)*f/Q on Iio rho; compute its derivative at 0
  let f : ℝ → ℝ := beukersAReal a
  let g : ℝ → ℝ := fun x => (a - x) * beukersAReal a x / beukersQuad a x
  have hg_eq : deriv f =ᶠ[𝓝 (0 : ℝ)] g := by
    have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
      exact isOpen_Iio.mem_nhds (by simpa using h0ρ)
    filter_upwards [hset] with x hx
    exact (beukersAReal_hasDerivAt a ha hx).deriv
  have hder : deriv (deriv f) 0 = deriv g 0 := by
    rw [hg_eq.deriv_eq]
  calc
    iteratedDeriv 2 (beukersAReal a) 0 = iteratedDeriv 1 (deriv f) 0 := by
      rw [iteratedDeriv_succ']
    _ = deriv (deriv f) 0 := by
      rw [iteratedDeriv_succ']
      simp
    _ = deriv g 0 := hder
    _ = 3 * a ^ 2 - 1 := by
        -- compute HasDerivAt g (3a^2-1) 0 via quotient rule at 0
        have hf0 : HasDerivAt f a 0 := by
          have hd := beukersAReal_hasDerivAt a ha h0ρ
          have hd' : HasDerivAt (beukersAReal a) a 0 := by
            convert hd using 1
            rw [beukersAReal_zero_value]
            dsimp [beukersQuad]
            norm_num
          simpa [f] using hd'
        have hf0v : f 0 = 1 := by
          simpa [f] using beukersAReal_zero_value a
        let num : ℝ → ℝ := fun x => (a - x) * f x
        have hnum : HasDerivAt num (a * a - 1) 0 := by
          have hlin : HasDerivAt (fun x : ℝ => a - x) (-1) 0 := HasDerivAt.const_sub a (hasDerivAt_id 0)
          have hpr := hlin.mul hf0
          have hprv : (-1) * f 0 + (a - 0) * a = a * a - 1 := by
            rw [hf0v]
            ring
          have hpr' : HasDerivAt (fun x : ℝ => (a - x) * f x) (a * a - 1) 0 := by
            rwa [hprv] at hpr
          simpa [num] using hpr'
        have hden0 : beukersQuad a 0 ≠ 0 := by
          dsimp [beukersQuad]
          norm_num
        have hden : HasDerivAt (beukersQuad a) (2 * 0 - 2 * a) 0 := beukersQuad_hasDerivAt a 0
        have hquot := hnum.div hden hden0
        have hqval : ((a * a - 1) * beukersQuad a 0 - (a - 0) * f 0 * (2 * 0 - 2 * a)) /
              (beukersQuad a 0) ^ 2 = 3 * a ^ 2 - 1 := by
          rw [hf0v]
          dsimp [beukersQuad]
          ring
        have hpoint : num / beukersQuad a = g := by
          dsimp [num, g]
          funext x
          rfl
        have hg : HasDerivAt g (3 * a ^ 2 - 1) 0 := by
          rw [← hpoint]
          rw [hqval] at hquot
          exact hquot
        exact hg.deriv


-- ============ the real coefficient sequence beukersUR and the bridge ============

/-- real-parametrized Beukers coefficients, mirroring `beukersU` over `ℚ` -/
def beukersUR (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => a
  | n + 2 =>
      (((2 * (n : ℝ)) + 3) * a * beukersUR a (n + 1) - ((n : ℝ) + 1) * beukersUR a n) /
        ((n : ℝ) + 2)

lemma beukersUR_zero (a : ℝ) : beukersUR a 0 = 1 := rfl

lemma beukersUR_one (a : ℝ) : beukersUR a 1 = a := rfl

lemma beukersUR_step (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * beukersUR a (n + 2) =
      ((2 * (n : ℝ)) + 3) * a * beukersUR a (n + 1) - ((n : ℝ) + 1) * beukersUR a n := by
  simp [beukersUR]
  field_simp

/-- the real coefficient sequence with rational parameter `ã` is the cast of `beukersU` -/
lemma beukersUR_eq_cast (ã : ℚ) (n : ℕ) : beukersUR (ã : ℝ) n = (beukersU ã n : ℝ) := by
  refine Nat.strong_induction_on n ?_
  clear n
  intro n hind
  by_cases hn0 : n = 0
  · subst n; simp [beukersUR, beukersU]
  · by_cases hn1 : n = 1
    · subst n; simp [beukersUR, beukersU]
    · rcases n with _ | _ | n
      · omega
      · omega
      have hprev2 : beukersUR (ã : ℝ) (n + 1) = (beukersU ã (n + 1) : ℝ) := hind (n + 1) (by omega)
      have hprev1 : beukersUR (ã : ℝ) n = (beukersU ã n : ℝ) := hind n (by omega)
      have hnz : ((n : ℝ) + 2) ≠ 0 := by positivity
      have hA := beukersUR_step (ã : ℝ) n
      have hLHS : ((n : ℝ) + 2) * beukersUR (ã : ℝ) (n + 2) =
          ((2 * (n : ℝ)) + 3) * (ã : ℝ) * (beukersU ã (n + 1) : ℝ) -
            ((n : ℝ) + 1) * (beukersU ã n : ℝ) := by
        rw [hA, hprev2, hprev1]
      have hBcast : ((n : ℝ) + 2) * (beukersU ã (n + 2) : ℝ) =
          ((2 * (n : ℝ)) + 3) * (ã : ℝ) * (beukersU ã (n + 1) : ℝ) -
            ((n : ℝ) + 1) * (beukersU ã n : ℝ) := by
        exact_mod_cast (beukersU_step ã n)
      have hprod : ((n : ℝ) + 2) * beukersUR (ã : ℝ) (n + 2) =
          ((n : ℝ) + 2) * (beukersU ã (n + 2) : ℝ) := by
        rw [hLHS]
        exact hBcast.symm
      exact (mul_left_cancel₀ hnz hprod)

-- ============ coefficient bridge for AReal ============

/-- recurrence for the iterated derivatives at index m >= 1 -/
lemma beukersAReal_iterDeriv_step_all (a : ℝ) (ha : 3 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv (m + 1) (beukersAReal a) 0 =
      a * ((2 * (m : ℝ)) + 1) * iteratedDeriv m (beukersAReal a) 0 -
        ((m : ℝ) ^ 2) * iteratedDeriv (m - 1) (beukersAReal a) 0 := by
  by_cases h1 : m = 1
  · subst m
    -- e2 = 3a*e1 - e0
    have he2 := beukersAReal_iterDeriv_two a ha
    -- RHS: a*3*e1 - 1^2*e0 = 3a*a - 1
    have he1 : iteratedDeriv 1 (beukersAReal a) 0 = a := by
      rw [iteratedDeriv_succ']
      simp
      exact beukersAReal_deriv_zero a ha
    have he0 : iteratedDeriv 0 (beukersAReal a) 0 = 1 := by
      simpa using beukersAReal_zero_value a
    rw [he2, he1, he0]
    ring
  · have hm2 : 2 ≤ m := by omega
    exact beukersAReal_iterDeriv_step a ha m hm2

/-- abstract arithmetic step of the coefficient bridge (all in `ℝ`) -/
private lemma beukers_bridge_step_arith {a n F1 F2 u0 u1 u2 : ℝ}
    (hstepR : n * u0 = (2 * n - 1) * a * u1 - (n - 1) * u2)
    (hfac2 : F1 = (n - 1) * F2) :
    a * (2 * (n - 1) + 1) * (F1 * u1) - (n - 1) ^ 2 * (F2 * u2) = n * F1 * u0 := by
  calc
    a * (2 * (n - 1) + 1) * (F1 * u1) - (n - 1)^2 * (F2 * u2)
        = a * (2*n - 1) * (F1 * u1) - (n - 1) * F1 * u2 := by
            have h2 : (n - 1)^2 * (F2 * u2) = (n - 1) * F1 * u2 := by
              calc (n - 1)^2 * (F2*u2) = (n - 1)*((n - 1)*F2)*u2 := by ring
              _ = (n - 1) * F1 * u2 := by rw [← hfac2]
            rw [h2]
            ring
    _ = F1 * ((2*n - 1) * a * u1 - (n - 1) * u2) := by ring
    _ = F1 * (n * u0) := by rw [← hstepR]
    _ = n * F1 * u0 := by ring

/-- **coefficient bridge**: the iterated derivatives of `A(a,x)` at `0` are
`n!·u_n(a)` where `u_n` is the (real) Beukers coefficient sequence -/
lemma beukersAReal_iterDeriv_eq_fact (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    iteratedDeriv n (beukersAReal a) 0 = (n.factorial : ℝ) * beukersUR a n := by
  refine Nat.strong_induction_on n ?_
  clear n
  intro n hind
  by_cases hn0 : n = 0
  · subst n
    have he0 : iteratedDeriv 0 (beukersAReal a) 0 = 1 := by
      simpa using beukersAReal_zero_value a
    rw [he0]
    simp [beukersUR]
  · by_cases hn1 : n = 1
    · subst n
      have he1 : iteratedDeriv 1 (beukersAReal a) 0 = a := by
        rw [iteratedDeriv_succ']
        simp
        exact beukersAReal_deriv_zero a ha
      rw [he1]
      simp [beukersUR]
    · have hn2 : 2 ≤ n := by omega
      -- recurrence at m = n-1 >= 1
      have hrec := beukersAReal_iterDeriv_step_all a ha (n - 1) (by omega)
      have hprev1 : iteratedDeriv (n - 1) (beukersAReal a) 0 =
          ((n - 1).factorial : ℝ) * beukersUR a (n - 1) := hind (n - 1) (by omega)
      have hprev2 : iteratedDeriv (n - 2) (beukersAReal a) 0 =
          ((n - 2).factorial : ℝ) * beukersUR a (n - 2) := hind (n - 2) (by omega)
      have hsub1 : (n - 1) + 1 = n := by omega
      have hsub2 : (n - 1) - 1 = n - 2 := by omega
      rw [hsub1] at hrec
      rw [hsub2] at hrec
      rw [hrec, hprev1, hprev2]
      -- goal: a(2c1+1)·F1·u1 - c1^2·F2·u2 = n!·uN where c1 := ((n-1:ℕ):ℝ), F1 := ((n-1)!:ℝ), ...
      have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
        have hnat : n.factorial = n * (n - 1).factorial := by
          rcases n with _ | k
          · omega
          · rw [Nat.factorial_succ]
            simp
        rw [hnat, Nat.cast_mul]
      have hfac2 : ((n - 1).factorial : ℝ) = ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
        have hnat : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
          rcases n with _ | _ | k
          · omega
          · omega
          · simp
            rw [Nat.factorial_succ]
        rw [hnat, Nat.cast_mul]
      have hcast1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
        norm_num
      have hcast0 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
        norm_num
      rw [hfac]
      rw [hcast1]
      -- derive the step in real form
      have hstep := beukersUR_step a (n - 2)
      have h_idx1 : (n - 2) + 2 = n := by omega
      have h_idx2 : (n - 2) + 1 = n - 1 := by omega
      rw [h_idx1, h_idx2] at hstep
      rw [hcast0] at hstep
      have hstepR : (n : ℝ) * beukersUR a n =
          ((2 * (n : ℝ)) - 1) * a * beukersUR a (n - 1) - ((n : ℝ) - 1) * beukersUR a (n - 2) := by
        nlinarith [hstep]
      have hfac2r : ((n - 1).factorial : ℝ) = ((n : ℝ) - 1) * ((n - 2).factorial : ℝ) := by
        rw [hfac2, hcast1]
      -- invoke the abstract step identity
      exact beukers_bridge_step_arith (a := a) (n := (n : ℝ))
        (F1 := ((n - 1).factorial : ℝ)) (F2 := ((n - 2).factorial : ℝ))
        (u0 := beukersUR a n) (u1 := beukersUR a (n - 1)) (u2 := beukersUR a (n - 2))
        hstepR hfac2r



-- ============ analytic series identity on a neighborhood ============

/-- near `0` the real Beukers function equals its power series with
coefficients `u_n(a)`: `A(a,x) = Σₙ u_n(a)·xⁿ` -/
lemma beukersAReal_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ), HasSum (fun n : ℕ => beukersUR a n * x ^ n) (beukersAReal a x) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ
    (fun n => iteratedDeriv n (beukersAReal a) 0 / (n.factorial : ℝ))
  have hcanon : HasFPowerSeriesAt (beukersAReal a) p 0 := by
    simpa [p] using (AnalyticAt.hasFPowerSeriesAt (beukersAReal_analyticAt_zero a ha))
  have hcoeff : ∀ n : ℕ, p.coeff n = beukersUR a n := by
    intro n
    dsimp [p]
    rw [FormalMultilinearSeries.coeff_ofScalars]
    have hf := beukersAReal_iterDeriv_eq_fact a ha n
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [hf]
    field_simp [hnf]
  have hconv := (hasFPowerSeriesAt_iff.mp hcanon)
  filter_upwards [hconv] with x hx
  have hx' : HasSum (fun n : ℕ => x ^ n • p.coeff n) (beukersAReal a x) := by simpa using hx
  have hsum : HasSum (fun n : ℕ => x ^ n • beukersUR a n) (beukersAReal a x) := by
    refine hx'.congr_fun ?_
    intro n
    rw [hcoeff n]
  simpa [mul_comm, smul_eq_mul] using hsum


-- ============ WReal side: derivative bridge ============

/-- iterated derivatives of the companion antiderivative `W(a,·)` at `0`:
`W^{(n+1)}(0) = n!·u_n(a)` (since `W′ = A`) -/
lemma beukersWReal_iterDeriv_succ (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    iteratedDeriv (n + 1) (beukersWReal a) 0 = (n.factorial : ℝ) * beukersUR a n := by
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  have heq : deriv (beukersWReal a) =ᶠ[𝓝 (0 : ℝ)] beukersAReal a := by
    filter_upwards [hset] with x hx
    exact (beukersWReal_hasDerivAt a ha hx).deriv
  calc
    iteratedDeriv (n + 1) (beukersWReal a) 0 = iteratedDeriv n (deriv (beukersWReal a)) 0 := by
      rw [iteratedDeriv_succ']
    _ = iteratedDeriv n (beukersAReal a) 0 := by
      exact (Filter.EventuallyEq.iteratedDeriv_eq n heq)
    _ = (n.factorial : ℝ) * beukersUR a n := beukersAReal_iterDeriv_eq_fact a ha n

/-- coefficients of `W(a,·)`: `w_0 = 0` and `wₙ = u_{n−1}/n` for `n ≥ 1` -/
lemma beukersWReal_iterDeriv_eq (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    iteratedDeriv n (beukersWReal a) 0 =
      (n.factorial : ℝ) * (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    have hw : beukersWReal a 0 = 0 := beukersWReal_zero a
    simp [hw]
  · rcases n with _ | m
    · omega
    · -- n = m+1 ≥ 1
      have h := beukersWReal_iterDeriv_succ a ha m
      have hfact_div : ((m + 1).factorial : ℝ) * (beukersUR a m / ((m : ℝ) + 1)) =
          (m.factorial : ℝ) * beukersUR a m := by
        have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
          have hnat : (m + 1).factorial = (m + 1) * m.factorial := by
            rw [Nat.factorial_succ]
          rw [hnat, Nat.cast_mul]
          norm_num
        rw [hfac]
        have hnz : ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hnz]
      rw [if_neg (by omega : ¬m + 1 = 0)]
      rw [show m + 1 - 1 = m by omega]
      have hcast : ((m + 1 : ℕ) : ℝ) = ((m : ℝ) + 1) := by
        norm_num
      rw [hcast]
      rw [h]
      rw [hfact_div]


/-- near `0` the real companion antiderivative equals its power series:
`W(a,x) = Σₙ wₙ·xⁿ` with `w₀ = 0`, `wₙ = u_{n−1}(a)/n` -/
lemma beukersWReal_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)) * x ^ n)
        (beukersWReal a x) := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ
    (fun n => iteratedDeriv n (beukersWReal a) 0 / (n.factorial : ℝ))
  have hcanon : HasFPowerSeriesAt (beukersWReal a) p 0 := by
    simpa [p] using (AnalyticAt.hasFPowerSeriesAt (beukersWReal_analyticAt_zero a ha))
  have hcoeff : ∀ n : ℕ, p.coeff n = (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)) := by
    intro n
    dsimp [p]
    rw [FormalMultilinearSeries.coeff_ofScalars]
    have hf := beukersWReal_iterDeriv_eq a ha n
    have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [hf]
    field_simp [hnf]
  have hconv := (hasFPowerSeriesAt_iff.mp hcanon)
  filter_upwards [hconv] with x hx
  have hx' : HasSum (fun n : ℕ => x ^ n • p.coeff n) (beukersWReal a x) := by simpa using hx
  have hsum : HasSum (fun n : ℕ => x ^ n • (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)))
      (beukersWReal a x) := by
    refine hx'.congr_fun ?_
    intro n
    rw [hcoeff n]
  simpa [mul_comm, smul_eq_mul] using hsum



/-- rational-parameter form of the AReal series identity: for `ã : ℚ` with
`ã ≥ 3`, near `0` (real): `A(ã,x) = Σₙ (u_n(ã) : ℝ)·xⁿ` where `u_n(ã)` are
the rational Beukers coefficients (the form needed by the Theorem-C
application, `a = 1 + 2m` an odd integer) -/
lemma beukersAReal_hasSum_series_rational (ã : ℚ) (hã : 3 ≤ (ã : ℝ)) :
    ∀ᶠ x in 𝓝 (0 : ℝ), HasSum (fun n : ℕ => (beukersU ã n : ℝ) * x ^ n) (beukersAReal (ã : ℝ) x) := by
  have h := beukersAReal_hasSum_series (ã : ℝ) hã
  filter_upwards [h] with x hx
  refine hx.congr_fun ?_
  intro n
  rw [beukersUR_eq_cast ã n]


/-! ### A5 stage 2 (cont.) — the `H = A·W` coefficient half: Cauchy products and
`v_n(a)`

This section closes the coefficient bridge for the companion product.  It
proves, for real `a ≥ 3`, the **power-series product theorems** and their
application to the real companion functions:

* the generic series machinery (Commons
  `Commons.Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound` and
  `...powSeries_product_hasSum_of_abs_summable`): a power series whose
  coefficients grow geometrically converges absolutely inside its radius, and
  the product of two such series is the **Cauchy product** (`HasSum` of the
  convolution = product of the limits) — Mathlib's
  `hasSum_sum_range_mul_of_summable_norm` fed with geometric bounds;
* the growth of the real coefficients: `beukersUR_growth`
  (`∃ C ρ > 0, |u_n(a)| ≤ C·ρⁿ` — from the analyticity of `AReal` at `0` via
  the radius of its canonical series) and `beukersWSeq_growth` for the
  `W`-coefficients `w₀ = 0`, `wₙ = u_{n−1}/n` (`beukersWSeq`), hence the
  absolute summability near `0` of both series
  (`beukersAReal_series_abs_summable`, `beukersWSeq_series_abs_summable`);
* the **real companion coefficients** `beukersVR a n :=
  Σ_{j=1}^n u_{n−j}(a)·u_{j−1}(a)/j` (mirror of the rational `beukersV`;
  `beukersVR_eq_cast` = the cast of `beukersV`), the reindexing lemma
  `beukersVR_eq_range_conv` (the `[xⁿ](A·W)` convolution = `v_n(a)`); and
* **`beukersH_hasSum_series`**: near `0`,
  `A(a,x)·W(a,x) = Σₙ v_n(a)·xⁿ` (Cauchy product of the two convergent
  series), and **`beukers_hasSum_apéry_series`**:
  `A·(W−η_a) = Σₙ (v_n(a) − η_a·u_n(a))·xⁿ` near `0` — the η-dependence of
  the companion series made explicit (this is the series that the brick-A4
  function `F` must be compared with, and whose Cauchy coefficient bounds
  give `|v_n − η_a·u_n| ≤ C·r^{−n}`, brick A6).
-/

-- growth bound (H2)
lemma beukersUR_growth (a : ℝ) (ha : 3 ≤ a) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ n : ℕ, |beukersUR a n| ≤ C * ρ ^ n := by
  rcases Commons.Analysis.Analytic.coeff_growth_of_analyticAt (beukersAReal_analyticAt_zero a ha)
    with ⟨C, ρ, hC, hρ, hg⟩
  refine ⟨C, ρ, hC, hρ, ?_⟩
  intro n
  have hnf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hc : beukersUR a n = iteratedDeriv n (beukersAReal a) 0 / (n.factorial : ℝ) := by
    have hf := beukersAReal_iterDeriv_eq_fact a ha n
    calc
      beukersUR a n = (n.factorial : ℝ) * beukersUR a n / (n.factorial : ℝ) := by
          field_simp [hnf]
      _ = iteratedDeriv n (beukersAReal a) 0 / (n.factorial : ℝ) := by rw [← hf]
  calc
    |beukersUR a n| = |iteratedDeriv n (beukersAReal a) 0 / (n.factorial : ℝ)| := by rw [hc]
    _ ≤ C * ρ ^ n := hg n

def beukersWSeq (a : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)

/-- W-coefficients grow geometrically (inherited from `u`) -/
lemma beukersWSeq_growth (a : ℝ) (ha : 3 ≤ a) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ n : ℕ, |beukersWSeq a n| ≤ C * ρ ^ n := by
  rcases beukersUR_growth a ha with ⟨C, ρ, hC, hρ, hu⟩
  refine ⟨C / ρ, ρ, by positivity, hρ, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    dsimp [beukersWSeq]
    simp
    positivity
  · have hn1 : 1 ≤ n := by omega
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
    have hnℝ : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hrel : (C / ρ) * ρ ^ n = C * ρ ^ (n - 1) := by
      have hsucc : (n - 1) + 1 = n := by omega
      have hpowstep : ρ ^ n = ρ ^ (n - 1) * ρ := by
        calc
          ρ ^ n = ρ ^ ((n - 1) + 1) := by congr 1; exact hsucc.symm
          _ = ρ * ρ ^ (n - 1) := pow_succ' ρ (n - 1)
          _ = ρ ^ (n - 1) * ρ := by rw [mul_comm]
      have hdiv : (C / ρ) * (ρ ^ (n - 1) * ρ) = C * ρ ^ (n - 1) := by
        field_simp [ne_of_gt hρ]
      calc
        (C / ρ) * ρ ^ n = (C / ρ) * (ρ ^ (n - 1) * ρ) := by rw [hpowstep]
        _ = C * ρ ^ (n - 1) := hdiv
    calc
      |beukersWSeq a n| = |beukersUR a (n - 1)| / (n : ℝ) := by
          dsimp [beukersWSeq]
          rw [if_neg hn]
          rw [abs_div]
          rw [abs_of_pos hnp]
      _ ≤ |beukersUR a (n - 1)| := by
          rw [div_le_iff₀ hnp]
          have : |beukersUR a (n - 1)| ≤ (n : ℝ) * |beukersUR a (n - 1)| := by
            calc
              |beukersUR a (n - 1)| = 1 * |beukersUR a (n - 1)| := by rw [one_mul]
              _ ≤ (n : ℝ) * |beukersUR a (n - 1)| := by
                  exact mul_le_mul_of_nonneg_right hnℝ (abs_nonneg _)
          simpa [mul_comm] using this
      _ ≤ C * ρ ^ (n - 1) := hu (n - 1)
      _ = (C / ρ) * ρ ^ n := hrel.symm


-- ============ summability eventual, beukersVR coefficients, product lemma ============

lemma beukersAReal_series_abs_summable (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ), Summable (fun n : ℕ => |beukersUR a n * x ^ n|) := by
  rcases beukersUR_growth a ha with ⟨C, ρ, hC, hρ, hu⟩
  have hset : Metric.ball (0 : ℝ) (1 / ρ) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hset] with x hx
  have hxabs : |x| < 1 / ρ := by
    simpa [Real.dist_eq] using hx
  have hxρ : ρ * |x| < 1 := by
    have hxρ' : |x| * ρ < 1 := (lt_div_iff₀ hρ).mp hxabs
    nlinarith
  exact Commons.Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound (le_of_lt hC) (le_of_lt hρ) hu hxρ

lemma beukersWSeq_series_abs_summable (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ), Summable (fun n : ℕ => |beukersWSeq a n * x ^ n|) := by
  rcases beukersWSeq_growth a ha with ⟨C, ρ, hC, hρ, hw⟩
  have hset : Metric.ball (0 : ℝ) (1 / ρ) ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hset] with x hx
  have hxabs : |x| < 1 / ρ := by
    simpa [Real.dist_eq] using hx
  have hxρ : ρ * |x| < 1 := by
    have hxρ' : |x| * ρ < 1 := (lt_div_iff₀ hρ).mp hxabs
    nlinarith
  exact Commons.Analysis.InfiniteSum.powSeries_abs_summable_of_geom_bound (le_of_lt hC) (le_of_lt hρ) hw hxρ

/-- real companion coefficients `v_n(a) = Σ_{j=1}^{n} u_{n−j}(a)·u_{j−1}(a)/j`
(mirror of the rational `beukersV`) -/
def beukersVR (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, beukersUR a (n - j) * (beukersUR a (j - 1) / (j : ℝ))

/-- the `[xⁿ](A·W)` convolution equals `v_n(a)` (real reindex, mirror of the
rational `beukersV_eq_sum_aux`) -/
lemma beukersVR_eq_range_conv (a : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), beukersUR a k *
        (if n - k = 0 then 0 else beukersUR a (n - k - 1) / ((n - k : ℕ) : ℝ)))
      = beukersVR a n := by
  calc
    (∑ k ∈ Finset.range (n + 1), beukersUR a k *
        (if n - k = 0 then 0 else beukersUR a (n - k - 1) / ((n - k : ℕ) : ℝ)))
        = ∑ k ∈ Finset.range n, beukersUR a k *
            (beukersUR a (n - k - 1) / ((n - k : ℕ) : ℝ)) := by
            rw [Finset.sum_range_succ]
            have hfn : (if n - n = 0 then (0 : ℝ) else beukersUR a (n - n - 1) / ((n - n : ℕ) : ℝ)) = 0 := by
              rw [Nat.sub_self]
              simp
            rw [hfn]
            simp
            apply Finset.sum_congr rfl
            intro k hk
            have hnk : n - k ≠ 0 := by
              have hk' : k < n := Finset.mem_range.mp hk
              omega
            rw [if_neg hnk]
    _ = ∑ j ∈ Finset.Icc 1 n, beukersUR a (n - j) * (beukersUR a (j - 1) / (j : ℝ)) := by
            refine Finset.sum_bij (fun k hk => n - k) ?_ ?_ ?_ ?_
            · intro k hk
              have hk' : k < n := Finset.mem_range.mp hk
              simp [Finset.mem_Icc]
              omega
            · intro k₁ hk₁ k₂ hk₂ h
              have hk₁' : k₁ < n := Finset.mem_range.mp hk₁
              have hk₂' : k₂ < n := Finset.mem_range.mp hk₂
              omega
            · intro j hj
              have hj₁ : 1 ≤ j := (Finset.mem_Icc.mp hj).1
              have hj₂ : j ≤ n := (Finset.mem_Icc.mp hj).2
              refine ⟨n - j, Finset.mem_range.mpr (by omega), ?_⟩
              omega
            · intro k hk
              have hk' : k < n := Finset.mem_range.mp hk
              have h₁ : n - (n - k) = k := by omega
              rw [h₁]
    _ = beukersVR a n := rfl

/-- rational-parameter `v_n`: the real companion coefficients are the cast of
`beukersV` -/
lemma beukersVR_eq_cast (ã : ℚ) (n : ℕ) : beukersVR (ã : ℝ) n = (beukersV ã n : ℝ) := by
  have hV := beukersV_eq_sum ã n
  rw [hV]
  dsimp [beukersVR]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [beukersUR_eq_cast ã (n - j), beukersUR_eq_cast ã (j - 1)]
  norm_num

/-- **`H = A·W` coefficient bridge**: near `0`, `A(a,x)·W(a,x)` equals its
power series with coefficients `v_n(a)` (real companion coefficients) -/
lemma beukersH_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => beukersVR a n * x ^ n) (beukersAReal a x * beukersWReal a x) := by
  filter_upwards [beukersAReal_hasSum_series a ha, beukersWReal_hasSum_series a ha,
    beukersAReal_series_abs_summable a ha, beukersWSeq_series_abs_summable a ha] with x hA hW hAabs hWabs
  -- convert the W-series statement to the beukersWSeq form
  have hW' : HasSum (fun n : ℕ => beukersWSeq a n * x ^ n) (beukersWReal a x) := by
    refine hW.congr_fun ?_
    intro n
    dsimp [beukersWSeq]
  have hprod := Commons.Analysis.InfiniteSum.powSeries_product_hasSum_of_abs_summable hA hW' hAabs hWabs
  -- hprod : HasSum (fun n => (∑ k∈range(n+1), u k·beukersWSeq(n-k))·x^n) (A·W)
  refine hprod.congr_fun ?_
  intro n
  dsimp [beukersWSeq]
  rw [beukersVR_eq_range_conv]

/-- **companion minus η·A**: near `0`,
`A·(W − η_a) = Σ (v_n(a) − η_a·u_n(a))·xⁿ` -/
lemma beukers_hasSum_apéry_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => (beukersVR a n - beukersEta a * beukersUR a n) * x ^ n)
        (beukersAReal a x * beukersWReal a x - beukersEta a * beukersAReal a x) := by
  filter_upwards [beukersH_hasSum_series a ha, beukersAReal_hasSum_series a ha] with x hH hA
  have hsub := hH.sub (hA.mul_left (beukersEta a))
  -- hsub : HasSum (fun n => beukersVR a n·xⁿ − η·(u n·xⁿ)) (A·W − η·A)
  refine hsub.congr_fun ?_
  intro n
  ring




/-- rational-parameter form of the Apéry-series identity: for `ã : ℚ` with
`ã ≥ 3`, near `0` (real): `A·(W−η_a) = Σₙ (v_n(ã) − η_a·u_n(ã))·xⁿ` with the
*rational* coefficients `u_n(ã)`, `v_n(ã)` (the form used by brick A6/A7 and
the Theorem-C application, `a = 1 + 2m` an odd integer) -/
lemma beukers_hasSum_apéry_series_rational (ã : ℚ) (hã : 3 ≤ (ã : ℝ)) :
    ∀ᶠ x in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => ((beukersV ã n : ℝ) - beukersEta (ã : ℝ) * (beukersU ã n : ℝ)) * x ^ n)
        (beukersAReal (ã : ℝ) x * beukersWReal (ã : ℝ) x -
          beukersEta (ã : ℝ) * beukersAReal (ã : ℝ) x) := by
  have h := beukers_hasSum_apéry_series (ã : ℝ) hã
  filter_upwards [h] with x hx
  refine hx.congr_fun ?_
  intro n
  rw [beukersVR_eq_cast ã n, beukersUR_eq_cast ã n]


/-! ### A5 stage 2 (cont.) — the complex-lift identification: Taylor
coefficients of `Aℂ` and `Wℂ` at `0`

The real-axis coefficient bridge (previous sections) is now lifted to the
complex functions.  The generic engine is the Commons lemma
`Commons.Analysis.Analytic.complex_coeff_eq_ofReal_axis`: if
a complex function `g` is analytic at `0` and agrees with the real-analytic
function `f` on the real axis near `0` (`g(↑x) = ↑(f x)`), then the Taylor
coefficients of `g` at `0` are the casts of the Taylor coefficients of `f`:

`g⁽ⁿ⁾(0)/n! = ↑(f⁽ⁿ⁾(0)/n!)`  (`ℂ`- vs `ℝ`-iterated derivatives).

Proof: both canonical power series are `HasSum` on their balls; restricting
to the real axis and subtracting gives, for every small real `t`, the
vanishing series `Σₙ bₙ·(t:ℂ)ⁿ = 0`, so all coefficients vanish
(`Commons.Analysis.InfiniteSum.hasSum_pow_eq_zero_of_eventually_zero`).

Applications (both with real coefficients equal to the real ones from the
A5 stage-2 real bridge):
* `beukersAComplex_coeff_eq`: Taylor coefficients of `Aℂ` at `0` are
  `u_n(a)` (real);
* `beukersWComplex_coeff_eq`: Taylor coefficients of `Wℂ` at `0` are
  `w₀ = 0`, `wₙ = u_{n−1}/n`.

Consequence (next sections): `Aℂ·(Wℂ−η_a)` has Taylor coefficients
`v_n(a) − η_a·u_n(a)` (real numbers), so the brick-A6 Cauchy estimates on
`|v_n − η_a·u_n|` become estimates on a holomorphic function's coefficients.
-/

/-- the Taylor coefficients of `Aℂ` at `0` equal `u_n(a)` -/
lemma beukersAComplex_coeff_eq (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    iteratedDeriv (𝕜 := ℂ) n (beukersAComplex a) 0 / (n.factorial : ℂ) =
      (beukersUR a n : ℂ) := by
  have hr : iteratedDeriv (𝕜 := ℝ) n (beukersAReal a) 0 / (n.factorial : ℝ) = beukersUR a n := by
    rw [beukersAReal_iterDeriv_eq_fact a ha n]
    field_simp
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  have heq : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), beukersAComplex a (x : ℂ) = (beukersAReal a x : ℂ) := by
    filter_upwards [hset] with x hx
    exact beukersAComplex_eq_ofReal a ha (by simpa using hx)
  have h := Commons.Analysis.Analytic.complex_coeff_eq_ofReal_axis (g := beukersAComplex a) (f := beukersAReal a)
    (beukersAComplex_analyticAt_zero a) (beukersAReal_analyticAt_zero a ha) heq n
  have hR : ((iteratedDeriv (𝕜 := ℝ) n (beukersAReal a) 0 : ℝ) : ℂ) /
      ((n.factorial : ℝ) : ℂ) = (beukersUR a n : ℂ) := by
    calc
      ((iteratedDeriv (𝕜 := ℝ) n (beukersAReal a) 0 : ℝ) : ℂ) /
          ((n.factorial : ℝ) : ℂ)
          = (((iteratedDeriv (𝕜 := ℝ) n (beukersAReal a) 0 / (n.factorial : ℝ)) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_div]
      _ = (beukersUR a n : ℂ) := by rw [hr]
  exact h.trans hR

/-- the Taylor coefficients of `Wℂ` at `0`: `w₀ = 0`, `wₙ = u_{n−1}/n` -/
lemma beukersWComplex_coeff_eq (a : ℝ) (ha : 3 ≤ a) (n : ℕ) :
    iteratedDeriv (𝕜 := ℂ) n (beukersWComplex a) 0 / (n.factorial : ℂ) =
      (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ) : ℂ) := by
  have hr : iteratedDeriv (𝕜 := ℝ) n (beukersWReal a) 0 / (n.factorial : ℝ) =
      (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ)) := by
    rw [beukersWReal_iterDeriv_eq a ha n]
    by_cases hn : n = 0
    · subst n; simp
    · rw [if_neg hn]
      field_simp
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  have heq : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), beukersWComplex a (x : ℂ) = (beukersWReal a x : ℂ) := by
    filter_upwards [hset] with x hx
    exact beukersWComplex_eq_ofReal a ha (by simpa using hx)
  have h := Commons.Analysis.Analytic.complex_coeff_eq_ofReal_axis (g := beukersWComplex a) (f := beukersWReal a)
    (beukersWComplex_analyticAt_zero a ha) (beukersWReal_analyticAt_zero a ha) heq n
  have hR : ((iteratedDeriv (𝕜 := ℝ) n (beukersWReal a) 0 : ℝ) : ℂ) /
      ((n.factorial : ℝ) : ℂ) = (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ) : ℂ) := by
    calc
      ((iteratedDeriv (𝕜 := ℝ) n (beukersWReal a) 0 : ℝ) : ℂ) /
          ((n.factorial : ℝ) : ℂ)
          = (((iteratedDeriv (𝕜 := ℝ) n (beukersWReal a) 0 / (n.factorial : ℝ)) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_div]
      _ = (if n = 0 then 0 else beukersUR a (n - 1) / (n : ℝ) : ℂ) := by
              rw [hr]
              by_cases hn : n = 0
              · subst n
                simp
              · rw [if_neg hn, if_neg hn]
                rw [Complex.ofReal_div]
  exact h.trans hR



/-! ### A5 stage 2 (cont.) — the complex product: `Aℂ·Wℂ` and `Aℂ·(Wℂ−η_a)`
series near complex `0`

The complex-lift coefficients (`beukersAComplex_coeff_eq`,
`beukersWComplex_coeff_eq`) now give the holomorphic power series at `0`:

* `beukersAComplex_hasSum_series`: near complex `0`,
  `Aℂ(z) = Σₙ (u_n(a):ℂ)·zⁿ`;
* `beukersWComplex_hasSum_series`: `Wℂ(z) = Σₙ (w_n:ℂ)·zⁿ` (with
  `wₙ = beukersWSeq a n`);
* absolute summability of both series on a disc (`beukersAComplex_series_abs_summable`,
  `beukersWComplex_series_abs_summable`, from the geometric growth of `u`,`w`);
* `beukersVR_conv_cast_eq`: the convolution of the cast coefficient sequences
  is the cast of `v_n(a)` (via `map_sum (algebraMap ℝ ℂ)` + `Complex.ofReal_mul`
  + `beukersVR_eq_range_conv`);
* **`beukersAComplexWComplex_hasSum_series`**: near complex `0`,
  `Aℂ(z)·Wℂ(z) = Σₙ (v_n(a):ℂ)·zⁿ` (the ℂ-version of the Cauchy product,
  `Commons.Analysis.InfiniteSum.powSeries_product_hasSum_of_abs_summable_complex`);
* **`beukers_hasSum_apéry_complex`** — the complex form of the companion
  identity: near complex `0`,
  `Aℂ(z)·(Wℂ(z)−η_a) = Σₙ (v_n(a) − η_a·u_n(a))·zⁿ`.

The right-hand series has real (indeed rational, for rational `a`)
coefficients, and its holomorphic sum on a neighbourhood of `0` is the object
whose analytic continuation through the singularity `ρ` (brick A6) is
controlled by the brick-A4 function `F`.
-/

lemma beukersAComplex_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), HasSum (fun n : ℕ => (beukersUR a n : ℂ) * z ^ n) (beukersAComplex a z) := by
  let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ
    (fun n => iteratedDeriv (𝕜 := ℂ) n (beukersAComplex a) 0 / (n.factorial : ℂ))
  have hcanon : HasFPowerSeriesAt (beukersAComplex a) pC 0 := by
    simpa [pC] using (AnalyticAt.hasFPowerSeriesAt (beukersAComplex_analyticAt_zero a))
  have hcoeff : ∀ n : ℕ, pC.coeff n = (beukersUR a n : ℂ) := by
    intro n
    dsimp [pC]
    rw [FormalMultilinearSeries.coeff_ofScalars]
    exact beukersAComplex_coeff_eq a ha n
  have hiff := (hasFPowerSeriesAt_iff.mp hcanon)
  filter_upwards [hiff] with z hz
  have hz' : HasSum (fun n : ℕ => (beukersUR a n : ℂ) * z ^ n) (beukersAComplex a (0 + z)) := by
    refine hz.congr_fun ?_
    intro n
    rw [hcoeff n, smul_eq_mul]
    ring
  simpa using hz'

/-- near complex `0`, `Wℂ(z) = Σₙ wₙ·zⁿ` with `wₙ = beukersWSeq a n` -/
lemma beukersWComplex_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => (beukersWSeq a n : ℂ) * z ^ n) (beukersWComplex a z) := by
  let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ
    (fun n => iteratedDeriv (𝕜 := ℂ) n (beukersWComplex a) 0 / (n.factorial : ℂ))
  have hcanon : HasFPowerSeriesAt (beukersWComplex a) pC 0 := by
    simpa [pC] using (AnalyticAt.hasFPowerSeriesAt (beukersWComplex_analyticAt_zero a ha))
  have hcoeff : ∀ n : ℕ, pC.coeff n = (beukersWSeq a n : ℂ) := by
    intro n
    dsimp [pC]
    rw [FormalMultilinearSeries.coeff_ofScalars]
    have h := beukersWComplex_coeff_eq a ha n
    rw [h]
    dsimp [beukersWSeq]
    by_cases hn : n = 0
    · subst n
      simp
    · rw [if_neg hn, if_neg hn]
      rw [Complex.ofReal_div]
      norm_num
  have hiff := (hasFPowerSeriesAt_iff.mp hcanon)
  filter_upwards [hiff] with z hz
  have hz' : HasSum (fun n : ℕ => (beukersWSeq a n : ℂ) * z ^ n) (beukersWComplex a (0 + z)) := by
    refine hz.congr_fun ?_
    intro n
    rw [hcoeff n, smul_eq_mul]
    ring
  simpa using hz'


/-- absolute summability of the `Aℂ` series near `0` (geometric growth of `u`) -/
lemma beukersAComplex_series_abs_summable (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖(beukersUR a n : ℂ) * z ^ n‖) := by
  rcases beukersUR_growth a ha with ⟨C, ρ, hC, hρ, hu⟩
  have hset : Metric.ball (0 : ℂ) (1 / ρ) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hset] with z hz
  have hzn : ‖z‖ < 1 / ρ := by simpa [Real.dist_eq, Complex.dist_eq] using hz
  have hzρ : ρ * ‖z‖ < 1 := by
    have hzρ' : ‖z‖ * ρ < 1 := (lt_div_iff₀ hρ).mp hzn
    nlinarith
  have hgeom : Summable (fun n : ℕ => (ρ * ‖z‖) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (le_of_lt hρ) (norm_nonneg z)) hzρ
  have hscaled : Summable (fun n : ℕ => C * (ρ * ‖z‖) ^ n) := hgeom.mul_left C
  refine .of_nonneg_of_le (fun n => norm_nonneg _) ?_ hscaled
  intro n
  calc
    ‖(beukersUR a n : ℂ) * z ^ n‖ = |beukersUR a n| * ‖z‖ ^ n := by
        simpa [RCLike.norm_ofReal (K := ℂ)] using
          (norm_mul (beukersUR a n : ℂ) (z ^ n)).trans (by congr 1; rw [norm_pow])
    _ ≤ (C * ρ ^ n) * ‖z‖ ^ n := by
        exact mul_le_mul_of_nonneg_right (hu n) (pow_nonneg (norm_nonneg z) n)
    _ = C * (ρ * ‖z‖) ^ n := by
        rw [mul_assoc, ← mul_pow]

/-- absolute summability of the `Wℂ` series near `0` (geometric growth of `w`) -/
lemma beukersWComplex_series_abs_summable (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), Summable (fun n : ℕ => ‖(beukersWSeq a n : ℂ) * z ^ n‖) := by
  rcases beukersWSeq_growth a ha with ⟨C, ρ, hC, hρ, hw⟩
  have hset : Metric.ball (0 : ℂ) (1 / ρ) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hset] with z hz
  have hzn : ‖z‖ < 1 / ρ := by simpa [Real.dist_eq, Complex.dist_eq] using hz
  have hzρ : ρ * ‖z‖ < 1 := by
    have hzρ' : ‖z‖ * ρ < 1 := (lt_div_iff₀ hρ).mp hzn
    nlinarith
  have hgeom : Summable (fun n : ℕ => (ρ * ‖z‖) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (le_of_lt hρ) (norm_nonneg z)) hzρ
  have hscaled : Summable (fun n : ℕ => C * (ρ * ‖z‖) ^ n) := hgeom.mul_left C
  refine .of_nonneg_of_le (fun n => norm_nonneg _) ?_ hscaled
  intro n
  calc
    ‖(beukersWSeq a n : ℂ) * z ^ n‖ = |beukersWSeq a n| * ‖z‖ ^ n := by
        simpa [RCLike.norm_ofReal (K := ℂ)] using
          (norm_mul (beukersWSeq a n : ℂ) (z ^ n)).trans (by congr 1; rw [norm_pow])
    _ ≤ (C * ρ ^ n) * ‖z‖ ^ n := by
        exact mul_le_mul_of_nonneg_right (hw n) (pow_nonneg (norm_nonneg z) n)
    _ = C * (ρ * ‖z‖) ^ n := by
        rw [mul_assoc, ← mul_pow]

/-- convolution of the cast coefficient sequences = cast of `v_n(a)` -/
lemma beukersVR_conv_cast_eq (a : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (beukersUR a k : ℂ) * (beukersWSeq a (n - k) : ℂ))
      = (beukersVR a n : ℂ) := by
  calc
    (∑ k ∈ Finset.range (n + 1), (beukersUR a k : ℂ) * (beukersWSeq a (n - k) : ℂ))
        = (∑ k ∈ Finset.range (n + 1), (((beukersUR a k * beukersWSeq a (n - k)) : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Complex.ofReal_mul]
    _ = (((∑ k ∈ Finset.range (n + 1), beukersUR a k * beukersWSeq a (n - k)) : ℝ) : ℂ) := by
            exact (map_sum (algebraMap ℝ ℂ)
              (fun k : ℕ => beukersUR a k * beukersWSeq a (n - k)) (Finset.range (n + 1))).symm
    _ = (beukersVR a n : ℂ) := by
            congr 1
            have hR : (∑ k ∈ Finset.range (n + 1), beukersUR a k * beukersWSeq a (n - k))
                = (∑ k ∈ Finset.range (n + 1), beukersUR a k *
                    (if n - k = 0 then 0 else beukersUR a (n - k - 1) / ((n - k : ℕ) : ℝ))) := by
                apply Finset.sum_congr rfl
                intro k hk
                dsimp [beukersWSeq]
            rw [hR]
            exact beukersVR_eq_range_conv a n

/-- **complex product statement**: near complex `0`, `Aℂ·Wℂ = Σₙ vₙ(a)·zⁿ` -/
lemma beukersAComplexWComplex_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => (beukersVR a n : ℂ) * z ^ n)
        (beukersAComplex a z * beukersWComplex a z) := by
  filter_upwards [beukersAComplex_hasSum_series a ha, beukersWComplex_hasSum_series a ha,
    beukersAComplex_series_abs_summable a ha, beukersWComplex_series_abs_summable a ha] with z hA hW hAabs hWabs
  have hprod := Commons.Analysis.InfiniteSum.powSeries_product_hasSum_of_abs_summable_complex
    (u := fun n : ℕ => (beukersUR a n : ℂ)) (v := fun n : ℕ => (beukersWSeq a n : ℂ))
    (x := z) (s := beukersAComplex a z) (t := beukersWComplex a z) hA hW hAabs hWabs
  refine hprod.congr_fun ?_
  intro n
  rw [beukersVR_conv_cast_eq a n]

/-- **`Aℂ·(Wℂ−η_a)` coefficient bridge (complex)**: near complex `0`,
`Aℂ·Wℂ − η_a·Aℂ = Σₙ (v_n(a) − η_a·u_n(a))·zⁿ` -/
lemma beukers_hasSum_apéry_complex (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((beukersVR a n - beukersEta a * beukersUR a n) : ℂ) * z ^ n)
        (beukersAComplex a z * beukersWComplex a z - (beukersEta a : ℂ) * beukersAComplex a z) := by
  filter_upwards [beukersAComplexWComplex_hasSum_series a ha, beukersAComplex_hasSum_series a ha] with z hH hA
  have hsub := hH.sub (hA.mul_left (beukersEta a : ℂ))
  refine hsub.congr_fun ?_
  intro n
  ring


/-! ### A6 — opening: the real-axis agreement of `Hℂ` with the real companion

The first layer of brick A6 (the analytic continuation of the companion
series and the Cauchy coefficient bounds).  The complex companion product

`Hℂ(z) := Aℂ(z)·(Wℂ(z) − η_a)`

(`beukersHComplex`) is holomorphic at `0` (`beukersHComplex_analyticAt_zero`)
with the power series `Σₙ (v_n(a) − η_a·u_n(a))·zⁿ`
(`beukersHComplex_hasSum_series`, restating the complex product theorem of
the previous section through the product definition).  The real-axis content:

* `beukersHComplex_eq_ofReal` — for real `x < ρ`,
  `Hℂ(↑x) = ↑(A(a,x)·W(a,x) − η_a·A(a,x))` (assembly of the real-axis
  agreements of `Aℂ`, `Wℂ`);
* `beukersHComplex_hasSum_series_realAxis` — restricting the holomorphic
  power series to the real axis: for real `x` near `0`,
  `Hℂ(↑x) = Σₙ ((v_n(a) − η_a·u_n(a)):ℂ)·(↑x)ⁿ`; and
* `beukers_apéry_realAxis_equality` — **the equality of the two analytic
  objects on an interval around `0`**: on a real neighbourhood of `0`,
  `Hℂ(↑x) = ↑(A(a,x)·W(a,x) − η_a·A(a,x))`.

Together with the real-series identity `beukers_hasSum_apéry_series`
(`A(a,x)·(W(a,x)−η_a) = Σₙ (v_n(a) − η_a·u_n(a))·xⁿ` near `0`, committed in
the A5 stage-2 section) this identifies the coefficient sequence
`v_n(a) − η_a·u_n(a)` with the power series of both the real companion
function and the restricted `Hℂ` on a common interval around `0` — the
starting point of the continuation/Cauchy argument (the continuation through
`x = ρ` is represented, on the real axis below `ρ`, by the descended
function `F` of brick A4, `beukersF_real_axis`).
-/

/-- the complex companion product `Hℂ(z) = Aℂ(z)·(Wℂ(z) − η_a)` (the
holomorphic object whose power series at `0` has the coefficients
`v_n(a) − η_a·u_n(a)`) -/
noncomputable def beukersHComplex (a : ℝ) (z : ℂ) : ℂ :=
  beukersAComplex a z * (beukersWComplex a z - (beukersEta a : ℂ))

/-- `Hℂ` is holomorphic at `0` -/
lemma beukersHComplex_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) :
    AnalyticAt ℂ (beukersHComplex a) 0 := by
  have hW : AnalyticAt ℂ (fun z : ℂ => beukersWComplex a z - (beukersEta a : ℂ)) 0 :=
    (beukersWComplex_analyticAt_zero a ha).sub (analyticAt_const (𝕜 := ℂ) (v := (beukersEta a : ℂ)) (x := (0 : ℂ)))
  exact (beukersAComplex_analyticAt_zero a).mul hW

/-- **real-axis agreement**: for real `x < ρ`,
`Hℂ(↑x) = ↑(A(a,x)·W(a,x) − η_a·A(a,x))` -/
lemma beukersHComplex_eq_ofReal (a : ℝ) (ha : 3 ≤ a) {x : ℝ} (hxρ : x < beukersRho a) :
    beukersHComplex a (x : ℂ) =
      ((beukersAReal a x * beukersWReal a x - beukersEta a * beukersAReal a x) : ℂ) := by
  dsimp [beukersHComplex]
  rw [beukersAComplex_eq_ofReal a ha hxρ]
  rw [beukersWComplex_eq_ofReal a ha hxρ]
  ring

/-- the power series of `Hℂ` at complex `0` — `Σ (v_n(a) − η_a·u_n(a))·zⁿ` -/
lemma beukersHComplex_hasSum_series (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((beukersVR a n - beukersEta a * beukersUR a n) : ℂ) * z ^ n)
        (beukersHComplex a z) := by
  have h := beukers_hasSum_apéry_complex a ha
  filter_upwards [h] with z hz
  have hv : beukersAComplex a z * beukersWComplex a z - (beukersEta a : ℂ) * beukersAComplex a z
      = beukersHComplex a z := by
    dsimp [beukersHComplex]
    ring
  simpa [hv] using hz

/-- **A6, first lemma** — the real-axis power series of `Hℂ`: for real `x`
near `0`, `Hℂ(↑x) = Σ ((v_n − η_a·u_n):ℂ)·(↑x)ⁿ` -/
lemma beukersHComplex_hasSum_series_realAxis (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
      HasSum (fun n : ℕ => ((beukersVR a n - beukersEta a * beukersUR a n) : ℂ) * (x : ℂ) ^ n)
        (beukersHComplex a (x : ℂ)) := by
  have hC := beukersHComplex_hasSum_series a ha
  exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).eventually hC


/-- **A6, equality of the two functions on an interval around `0`**: on a
real neighbourhood of `0`, the complex companion `Hℂ` restricted to the real
axis equals the cast of the real companion function `A·W − η_a·A` -/
lemma beukers_apéry_realAxis_equality (a : ℝ) (ha : 3 ≤ a) :
    ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
      beukersHComplex a (x : ℂ) =
        ((beukersAReal a x * beukersWReal a x - beukersEta a * beukersAReal a x) : ℂ) := by
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using (beukers_rho_pos a ha))
  filter_upwards [hset] with x hx
  exact beukersHComplex_eq_ofReal a ha (by simpa using hx)


/-! ### A6 — continuation (first stone): holomorphy along the interval and the
overlap with `F`

The first layer of the analytic-continuation argument that will extend the
companion series `Σ (v_n − η_a·u_n)·zⁿ` from its neighbourhood of `0` past
the singularity `ρ`.  Two prerequisites are laid down:

* **holomorphy at every point of the interval below `ρ`**:
  `beukersAComplex_analyticAt_of_slitPlane` (`Aℂ` holomorphic at any `w`
  with `Q(w)` in the slit plane — `√` is holomorphic there and its value is
  nonzero), `beukersWComplex_analyticAt_of_domain` (`Wℂ` holomorphic on the
  holomorphy domain `beukersWComplexDomain`), and hence
  `beukersHComplex_analyticAt_of_domain` / `beukersHComplex_analyticAt_ofReal_lt`
  (`Hℂ` holomorphic at every real point `x₀ < ρ`) — the real interval
  `(0, ρ)` is a genuine continuation path from `0` to `ρ` on which `Hℂ`
  agrees with the real companion (`beukersHComplex_eq_ofReal`);
* **the overlap with the brick-A4 descent**: for a descended `F`
  (`F(u²) = G0(u)` near `0`), `beukers_continuation_overlap` gives
  `ε > 0` with `F(↑t) = Hℂ(↑(ρ−t))` for all `0 < t < ε` — the `F`-side
  (analytic through `x = ρ`) and the `Hℂ`-side (analytic from `0`) take the
  same values on the real segment just below `ρ`, so the two anchored ends
  of the continuation overlap.

These are the local pieces out of which the global continuation (disc of
radius `> 1/a` around `0`) and the Cauchy coefficient bounds
(`|v_n − η_a·u_n| ≤ C r^{−n}`) are to be assembled next.
-/

/-- `Aℂ = 1/√Q` is holomorphic at any `w` with `Q(w)` in the slit plane -/
lemma beukersAComplex_analyticAt_of_slitPlane (a : ℝ) {w : ℂ}
    (hw : beukersQuadC a w ∈ Complex.slitPlane) : AnalyticAt ℂ (beukersAComplex a) w := by
  have hQ0 : AnalyticAt ℂ (fun z : ℂ => 1 - 2 * (a : ℂ) * z + z ^ 2) w := by
    fun_prop
  have hQ' : AnalyticAt ℂ (fun z : ℂ => beukersQuadC a z) w := by
    simpa [beukersQuadC] using hQ0
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (beukersQuadC a z)) w := by
    exact (Commons.Analysis.Complex.sqrt_analyticAt (z := beukersQuadC a w) hw).comp hQ'
  have hsqrt0ne : Complex.sqrt (beukersQuadC a w) ≠ 0 := by
    exact Commons.Analysis.Complex.sqrt_ne_zero_of_mem_slitPlane hw
  have hinv : AnalyticAt ℂ (fun z : ℂ => (Complex.sqrt (beukersQuadC a z))⁻¹) w :=
    hs.inv hsqrt0ne
  change AnalyticAt ℂ (fun z : ℂ => (Complex.sqrt (beukersQuadC a z))⁻¹) w
  exact hinv

/-- `Wℂ = log((a+1)/(a−z+√Q(z)))` is holomorphic at any point of its domain -/
lemma beukersWComplex_analyticAt_of_domain (a : ℝ) (ha : 3 ≤ a) {w : ℂ}
    (hw : w ∈ beukersWComplexDomain a) : AnalyticAt ℂ (beukersWComplex a) w := by
  rw [beukersWComplexDomain] at hw
  rcases hw with ⟨hwQ, hwR⟩
  have hQ0 : AnalyticAt ℂ (fun z : ℂ => 1 - 2 * (a : ℂ) * z + z ^ 2) w := by
    fun_prop
  have hQ' : AnalyticAt ℂ (fun z : ℂ => beukersQuadC a z) w := by
    simpa [beukersQuadC] using hQ0
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (beukersQuadC a z)) w := by
    exact (Commons.Analysis.Complex.sqrt_analyticAt (z := beukersQuadC a w) hwQ).comp hQ'
  have hid : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) - z) w := by
    fun_prop
  have hden : AnalyticAt ℂ (fun z : ℂ => (a : ℂ) - z + Complex.sqrt (beukersQuadC a z)) w :=
    hid.add hs
  -- den ≠ 0 at w (from the log argument in slitPlane; num = a+1 ≠ 0)
  have hnum_ne : (((a + 1 : ℝ) : ℂ)) ≠ 0 := by
    have h : (a + 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast h
  have hden_ne : (a : ℂ) - w + Complex.sqrt (beukersQuadC a w) ≠ 0 := by
    intro hd
    have hzero : (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - w + Complex.sqrt (beukersQuadC a w))) = 0 := by
      rw [hd]
      simp
    rw [hzero] at hwR
    rw [Complex.mem_slitPlane_iff] at hwR
    simp at hwR
  have hnum : AnalyticAt ℂ (fun z : ℂ => (((a + 1 : ℝ) : ℂ))) w := by
    fun_prop
  have hratio : AnalyticAt ℂ
      (fun z : ℂ => (((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z)))) w :=
    hnum.div hden hden_ne
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => Complex.log
        ((((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z))))) w :=
    AnalyticAt.clog hratio hwR
  change AnalyticAt ℂ
    (fun z : ℂ => Complex.log
      ((((a + 1 : ℝ) : ℂ) / ((a : ℂ) - z + Complex.sqrt (beukersQuadC a z))))) w
  exact hlog

/-- `Hℂ = Aℂ·(Wℂ−η_a)` is holomorphic at any point of the holomorphy domain -/
lemma beukersHComplex_analyticAt_of_domain (a : ℝ) (ha : 3 ≤ a) {w : ℂ}
    (hw : w ∈ beukersWComplexDomain a) : AnalyticAt ℂ (beukersHComplex a) w := by
  dsimp [beukersWComplexDomain] at hw
  rcases hw with ⟨hwQ, hwR⟩
  have hA := beukersAComplex_analyticAt_of_slitPlane a hwQ
  have hW := beukersWComplex_analyticAt_of_domain a ha (by
    dsimp [beukersWComplexDomain]
    exact ⟨hwQ, hwR⟩)
  have hWsub : AnalyticAt ℂ (fun z : ℂ => beukersWComplex a z - (beukersEta a : ℂ)) w :=
    hW.sub (analyticAt_const (𝕜 := ℂ) (v := (beukersEta a : ℂ)) (x := w))
  have hprod := hA.mul hWsub
  change AnalyticAt ℂ ((beukersAComplex a) * (fun z : ℂ => beukersWComplex a z - (beukersEta a : ℂ))) w
  exact hprod

/-- `Hℂ` is holomorphic at every real point `x₀ < ρ` of the interval below
the singularity (the continuation path from `0` to `ρ`) -/
lemma beukersHComplex_analyticAt_ofReal_lt (a : ℝ) (ha : 3 ≤ a) {x₀ : ℝ}
    (hx₀ : x₀ < beukersRho a) : AnalyticAt ℂ (beukersHComplex a) (x₀ : ℂ) := by
  have hdom : (x₀ : ℂ) ∈ beukersWComplexDomain a := beukersWComplexDomain_ofReal a ha hx₀
  exact beukersHComplex_analyticAt_of_domain a ha hdom

/-- **the first overlap/extension lemma of the continuation**: for a
descended `F` (brick A4), the `F`-side values just below the singularity
(`t ∈ (0, ε)`, `x = ρ − t`) equal the values of the holomorphic companion
`Hℂ` (coming from `0`) at the same points — the two anchored ends of the
continuation agree on their real-axis overlap -/
lemma beukers_continuation_overlap (a : ℝ) (ha : 3 ≤ a) {F : ℂ → ℂ}
    (hFeq : ∀ᶠ u in 𝓝 (0 : ℂ), F (u ^ 2) = beukersG0 a ha u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      F (t : ℂ) = beukersHComplex a (((beukersRho a - t : ℝ)) : ℂ) := by
  rcases beukersF_real_axis a ha hFeq with ⟨ε, hε0, hF⟩
  refine ⟨ε, hε0, ?_⟩
  intro t ht0 htε
  have hF' := hF t ht0 htε
  -- hF' : F(t:ℂ) = ↑(AReal(ρ−t)·(WReal(ρ−t) − η))
  have hxρ : beukersRho a - t < beukersRho a := by linarith
  have hx0 : beukersRho a - t < beukersRho a := hxρ
  have heq := beukersHComplex_eq_ofReal a ha (x := beukersRho a - t) hxρ
  -- heq : HComplex(↑(ρ−t)) = ↑(A(ρ−t)·W(ρ−t) − η·A(ρ−t))
  calc
    F (t : ℂ) = (((beukersAReal a (beukersRho a - t) * (beukersWReal a (beukersRho a - t) - beukersEta a)) : ℝ) : ℂ) := hF'
    _ = beukersHComplex a (((beukersRho a - t : ℝ)) : ℂ) := by
        rw [beukersHComplex_eq_ofReal a ha (x := beukersRho a - t) hx0]
        rw [Complex.ofReal_mul]
        rw [Complex.ofReal_sub]
        ring


/-! ### A6 — global (germ gluing along the continuation interval)

The second layer of the continuation: the real companion function of the
Apéry series,

`G_a(x) := A(a,x)·W(a,x) − η_a·A(a,x)`  (= `A(a,x)·(W(a,x) − η_a)`,
`beukersRealApéry`, `beukersRealApéry_eq`),

is real-analytic at **every** real `x₀ < ρ` (`beukersRealApéry_analyticAt`):
it is the real part of the holomorphic `Hℂ` restricted to the real axis, and
`Hℂ(↑x) = ↑G_a(x)` there (`beukersHComplex_eq_ofReal_eventually` — the
agreement localized at any point of the path).  The bundled gluing lemma
`beukers_apéry_germ_glue` records at each `x₀ < ρ`:

`AnalyticAt ℂ Hℂ ↑x₀ ∧ AnalyticAt ℝ G_a x₀ ∧ ∀ᶠ x in 𝓝 x₀, Hℂ(↑x) = ↑G_a(x)`.

Since `G_a` is one real-analytic function on the whole interval `(0, ρ)`, the
analytic germs of the continuation at overlapping points of the interval are
all the lifts of the germs of the same real-analytic `G_a` — the germ data
along the path is coherent, ready to be assembled (together with the overlap
lemma `beukers_continuation_overlap` at `ρ` and the power series at `0`) into
the global analytic continuation of `Σ (v_n − η_a·u_n) zⁿ`.
-/

/-- the real companion function of the Apéry series:
`G_a(x) := A(a,x)·W(a,x) − η_a·A(a,x)` (= `A(a,x)·(W(a,x) − η_a)`) -/
noncomputable def beukersRealApéry (a x : ℝ) : ℝ :=
  beukersAReal a x * beukersWReal a x - beukersEta a * beukersAReal a x

/-- the real companion equals `A·(W − η_a)` -/
lemma beukersRealApéry_eq (a x : ℝ) :
    beukersRealApéry a x = beukersAReal a x * (beukersWReal a x - beukersEta a) := by
  dsimp [beukersRealApéry]
  ring

/-- at each real `x₀ < ρ`, `Hℂ` agrees with the real companion on a whole real
neighbourhood of `x₀` (real-axis agreement localized at any point of the
continuation path) -/
lemma beukersHComplex_eq_ofReal_eventually (a : ℝ) (ha : 3 ≤ a) {x₀ : ℝ}
    (hx₀ : x₀ < beukersRho a) :
    ∀ᶠ x : ℝ in 𝓝 x₀, beukersHComplex a (x : ℂ) = (beukersRealApéry a x : ℂ) := by
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 x₀ := by
    exact isOpen_Iio.mem_nhds hx₀
  filter_upwards [hset] with x hx
  -- beukersHComplex_eq_ofReal: HComplex(↑x) = ↑(A·W − η·A); beukersRealApéry = A·W − η·A
  have hval := beukersHComplex_eq_ofReal a ha hx
  dsimp [beukersRealApéry]
  rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]
  exact hval

/-- **gluing fuel**: the real companion `G_a(x) = A(x)·W(x) − η_a·A(x)` is
real-analytic at every real `x₀ < ρ` (it is the real part of the holomorphic
`Hℂ` restricted to the real axis, and equals it there) -/
lemma beukersRealApéry_analyticAt (a : ℝ) (ha : 3 ≤ a) {x₀ : ℝ}
    (hx₀ : x₀ < beukersRho a) : AnalyticAt ℝ (beukersRealApéry a) x₀ := by
  have hre : AnalyticAt ℝ (fun x : ℝ => (beukersHComplex a (x : ℂ)).re) x₀ :=
    AnalyticAt.re_ofReal (beukersHComplex_analyticAt_ofReal_lt a ha hx₀)
  apply hre.congr
  have hset : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 x₀ := by
    exact isOpen_Iio.mem_nhds hx₀
  filter_upwards [hset] with x hx
  have hval := beukersHComplex_eq_ofReal a ha hx
  dsimp [beukersRealApéry]
  rw [hval]
  simp

/-- **the gluing lemma**: at every point `x₀` of the continuation interval
below `ρ` the analytic germ of `Hℂ` at `↑x₀` is the lift of the real-analytic
germ of the companion `G_a` at `x₀`: both analyticities hold and the
restriction of `Hℂ` to the real axis agrees with `G_a` in a whole real
neighbourhood of `x₀`.  Since `G_a` is real-analytic at every point of
`(0, ρ)`, the germs of the continuation at overlapping points of the interval
are all restrictions of the same real-analytic function. -/
lemma beukers_apéry_germ_glue (a : ℝ) (ha : 3 ≤ a) {x₀ : ℝ}
    (hx₀ : x₀ < beukersRho a) :
    AnalyticAt ℂ (beukersHComplex a) (x₀ : ℂ) ∧
    AnalyticAt ℝ (beukersRealApéry a) x₀ ∧
    ∀ᶠ x : ℝ in 𝓝 x₀, beukersHComplex a (x : ℂ) = (beukersRealApéry a x : ℂ) := by
  exact ⟨beukersHComplex_analyticAt_ofReal_lt a ha hx₀,
    beukersRealApéry_analyticAt a ha hx₀,
    beukersHComplex_eq_ofReal_eventually a ha hx₀⟩


/-! ### A6 — assembly (the `ρ`-extension of the continuation)

The first assembly brick of the global continuation: through the singularity
`ρ`.  With `F` from the brick-A4 descent (`F(u²) = G0(u)` near `0`,
holomorphic at `0`), the candidate continuation is

`g(z) := F(ρ − z)`   (`beukersApéryRhoExt a F`, the branch-point coordinate
`w = ρ − z`):

* `beukersApéryRhoExt_analyticAt_rho` — `g` is holomorphic at `ρ`
  (composition of the affine map `z ↦ ρ − z` with the holomorphic `F`);
* `beukersApéryRhoExt_eq_HComplex_below` — on the real axis just below `ρ`,
  `g(↑(ρ−t)) = Hℂ(↑(ρ−t))` for all small `0 < t` (from the overlap lemma
  `beukers_continuation_overlap`);
* `beukers_apéry_rho_extension` — the bundle: `g` is holomorphic at `ρ` and
  agrees with the holomorphic companion `Hℂ` on a real neighbourhood of `ρ`
  from below: `g` is the analytic continuation of the companion product
  through the singularity.

The full assembly (extension of the power series `Σ(v_n − η_a u_n)zⁿ` from
`0` to a disc of radius `> 1/a`, then the Cauchy coefficient bounds) is to be
completed by joining this `ρ`-extension with the power series at `0` along
the real interval `(0, ρ)` (identity theorem, using the germ coherence
`beukers_apéry_germ_glue` of the previous section).
-/

/-- the `ρ`-extension of a descended function `F`: `g(z) = F(ρ − z)` — the
continuation candidate through the singularity `ρ` (in the `z`-plane, with
the branch-point coordinate `w = ρ − z`) -/
noncomputable def beukersApéryRhoExt (a : ℝ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (((beukersRho a : ℝ) : ℂ) - z)

/-- the `ρ`-extension is holomorphic at `ρ` when `F` is holomorphic at `0`
(composition of the affine map `z ↦ ρ − z` with `F`) -/
lemma beukersApéryRhoExt_analyticAt_rho (a : ℝ) (F : ℂ → ℂ)
    (hF : AnalyticAt ℂ F 0) : AnalyticAt ℂ (beukersApéryRhoExt a F) (beukersRho a : ℂ) := by
  have hZ : AnalyticAt ℂ (fun z : ℂ => ((beukersRho a : ℝ) : ℂ) - z) ((beukersRho a : ℝ) : ℂ) := by
    fun_prop
  have hF0 : AnalyticAt ℂ F (((beukersRho a : ℝ) : ℂ) - ((beukersRho a : ℝ) : ℂ)) := by
    simpa using hF
  have hcomp : AnalyticAt ℂ (F ∘ (fun z : ℂ => ((beukersRho a : ℝ) : ℂ) - z))
      ((beukersRho a : ℝ) : ℂ) :=
    hF0.comp (x := ((beukersRho a : ℝ) : ℂ)) hZ
  change AnalyticAt ℂ (fun z : ℂ => F (((beukersRho a : ℝ) : ℂ) - z)) ((beukersRho a : ℝ) : ℂ)
  exact hcomp

/-- on the real axis just below `ρ`, the `ρ`-extension equals the holomorphic
companion `Hℂ` — `g(↑(ρ−t)) = Hℂ(↑(ρ−t))` for small `0 < t` (from the
overlap lemma `beukers_continuation_overlap`) -/
lemma beukersApéryRhoExt_eq_HComplex_below (a : ℝ) (ha : 3 ≤ a) {F : ℂ → ℂ}
    (hFeq : ∀ᶠ u in 𝓝 (0 : ℂ), F (u ^ 2) = beukersG0 a ha u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      beukersApéryRhoExt a F (((beukersRho a - t : ℝ)) : ℂ) = beukersHComplex a (((beukersRho a - t : ℝ)) : ℂ) := by
  rcases beukers_continuation_overlap a ha hFeq with ⟨ε, hε0, hF⟩
  refine ⟨ε, hε0, ?_⟩
  intro t ht0 htε
  have hF' := hF t ht0 htε
  -- hF' : F(↑t) = HComplex(↑(ρ−t))
  have hsub : ((beukersRho a : ℝ) : ℂ) - (((beukersRho a - t : ℝ)) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_sub]
    congr 1
    ring
  dsimp [beukersApéryRhoExt]
  rw [hsub]
  exact hF'

/-- **the extension through `ρ` (assembly brick)**: with `F` from the
brick-A4 descent (`F(u²) = G0(u)` near `0`, holomorphic at `0`), the function
`g(z) = F(ρ−z)` is holomorphic at `ρ` and agrees with the holomorphic
companion `Hℂ` on a real neighbourhood of `ρ` from below — `g` is the
continuation of the companion product through the singularity -/
lemma beukers_apéry_rho_extension (a : ℝ) (ha : 3 ≤ a) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0)
    (hFeq : ∀ᶠ u in 𝓝 (0 : ℂ), F (u ^ 2) = beukersG0 a ha u) :
    AnalyticAt ℂ (beukersApéryRhoExt a F) (beukersRho a : ℂ) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      beukersApéryRhoExt a F (((beukersRho a - t : ℝ)) : ℂ) = beukersHComplex a (((beukersRho a - t : ℝ)) : ℂ) := by
  exact ⟨beukersApéryRhoExt_analyticAt_rho a F hF,
    beukersApéryRhoExt_eq_HComplex_below a ha hFeq⟩

/-! ### A6 — the real-axis bridge of the `ρ`-extension (whole interval)

The pointwise engine of the continuation.  The overlap lemma
`beukersApéryRhoExt_eq_HComplex_below` records the agreement of the
`ρ`-extension `g(z) = F(ρ−z)` with the holomorphic companion `Hℂ` only on a
real segment *just below* `ρ` (where `F` was anchored by `beukersF_real_axis`).
The purpose of this section is to upgrade that to the **whole real interval
`(0, ρ)`** — and in fact to every real `x` with `ρ − R0² < x < ρ` when `F`
descends `G0` on the `u`-ball of radius `R0`.

The mechanism is purely pointwise (no identity theorem is needed).  For a real
`0 < x < ρ` write `w = ρ − x ∈ (0, ρ)` and `u = √w ∈ (0, √ρ)`.  Then:

* `g(↑x) = F(↑(ρ−x)) = F(↑w)`;
* since `u < R0` (when `w < R0²`), the descent equation gives
  `F(↑w) = F((↑u)²) = G0(↑u)`;
* since `u < R_u` (when `w < 2√(a²−1)`, which holds for all `w < ρ`), the
  real-axis value `beukersG0_real_axis` gives
  `G0(↑u) = ↑(A(ρ−u²)·(W(ρ−u²) − η_a)) = ↑(A(x)·(W(x) − η_a))`;
* `beukersHComplex_eq_ofReal` gives the same value for `Hℂ(↑x)`.

The output is the **real-axis bridge**: `g = Hℂ` on the whole interval
`(0, ρ)`.  Since both functions are holomorphic at `0`, this set of common
values accumulates at `0`, so the germs coincide (`AnalyticAt`-level identity
theorem) — the next section turns that into the power-series statement needed
for the Cauchy coefficient bounds.
-/

/-- elementary radius comparison: `ρ_a < 2·√(a²−1)` for `a ≥ 3` (the
`u² = ρ − x`-coordinate disc `|u|² < 2√(a²−1)` covers all of `x < ρ`) -/
lemma beukers_rho_lt_two_sqrt (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) := by
  have hpos : (0 : ℝ) < 1 / a := by positivity
  linarith [beukers_rho_add_one_div_lt_two_sqrt a ha]

/-- **the real-axis bridge (general form)**: for a descended `F` (the descent
equation `F(z²) = G0(z)` on the whole `u`-ball of radius `R0`), the
`ρ`-extension `g(z) = F(ρ−z)` equals the holomorphic companion `Hℂ` at every
real point `x < ρ` whose distance `w = ρ − x` to the singularity fits in the
coordinate discs: `w < R0²` (so that the descent equation applies at
`u = √w`) and `w < 2√(a²−1)` (so that the real-axis value of `G0` applies).
No identity theorem is used — the proof is pointwise through the `u = √w`
coordinate. -/
lemma beukers_apéry_rho_extension_interval_gen (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    {F : ℂ → ℂ} (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z)
    {x : ℝ} (hxρ : x < beukersRho a)
    (hxR0 : beukersRho a - x < (R0 : ℝ) ^ 2)
    (hx2c : beukersRho a - x < 2 * Real.sqrt (a ^ 2 - 1)) :
    beukersApéryRhoExt a F (x : ℂ) = beukersHComplex a (x : ℂ) := by
  let w : ℝ := beukersRho a - x
  let u : ℝ := Real.sqrt w
  have hw0 : 0 < w := by
    dsimp [w]
    linarith
  have hwR0 : w < (R0 : ℝ) ^ 2 := by
    dsimp [w]
    exact hxR0
  have hw2c : w < 2 * Real.sqrt (a ^ 2 - 1) := by
    dsimp [w]
    exact hx2c
  have hwpos_le : 0 ≤ w := le_of_lt hw0
  have hu0 : 0 < u := by
    dsimp [u]
    exact Real.sqrt_pos.2 hw0
  have huR : u < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) := by
    dsimp [u]
    exact Real.sqrt_lt_sqrt hwpos_le hw2c
  have hu2 : u ^ 2 = w := by
    dsimp [u]
    exact Real.sq_sqrt hwpos_le
  have hR0nonneg : (0 : ℝ) ≤ (R0 : ℝ) := by
    exact R0.2
  have hR0pos : (0 : ℝ) < (R0 : ℝ) := by
    have h0R0sq : (0 : ℝ) < (R0 : ℝ) ^ 2 := lt_trans hw0 hwR0
    nlinarith
  have huR0 : ‖(u : ℂ)‖ < (R0 : ℝ) := by
    have hult : u < (R0 : ℝ) := by
      dsimp [u]
      exact (Real.sqrt_lt' hR0pos).2 hwR0
    have hu_nonneg : 0 ≤ u := le_of_lt hu0
    simpa [RCLike.norm_ofReal (K := ℂ), abs_of_nonneg hu_nonneg]
  have hdesc : F ((u : ℂ) ^ 2) = beukersG0 a ha (u : ℂ) := hFdesc (u : ℂ) huR0
  have hpu : ((u : ℂ) ^ 2) = (w : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact congrArg Complex.ofReal hu2
  have hG : beukersG0 a ha (u : ℂ) =
      ((beukersAReal a (beukersRho a - w) *
        (beukersWReal a (beukersRho a - w) - beukersEta a) : ℝ) : ℂ) := by
    have h1 := beukersG0_real_axis a ha hu0 huR
    rw [hu2] at h1
    exact h1
  have hFw : F (w : ℂ) =
      ((beukersAReal a (beukersRho a - w) *
        (beukersWReal a (beukersRho a - w) - beukersEta a) : ℝ) : ℂ) := by
    calc
      F (w : ℂ) = F ((u : ℂ) ^ 2) := by rw [hpu]
      _ = beukersG0 a ha (u : ℂ) := hdesc
      _ = ((beukersAReal a (beukersRho a - w) *
            (beukersWReal a (beukersRho a - w) - beukersEta a) : ℝ) : ℂ) := hG
  have hρw : beukersRho a - w = x := by
    dsimp [w]
    ring
  have hS : F (w : ℂ) = ((beukersAReal a x * (beukersWReal a x - beukersEta a) : ℝ) : ℂ) := by
    simpa [hρw] using hFw
  have hS2 : ((beukersAReal a x * (beukersWReal a x - beukersEta a) : ℝ) : ℂ) =
      beukersHComplex a (x : ℂ) := by
    rw [beukersHComplex_eq_ofReal a ha hxρ]
    rw [Complex.ofReal_mul]
    rw [Complex.ofReal_sub]
    ring
  have hgx : beukersApéryRhoExt a F (x : ℂ) = F ((w : ℝ) : ℂ) := by
    dsimp [beukersApéryRhoExt]
    congr 1
    rw [← Complex.ofReal_sub]
  calc
    beukersApéryRhoExt a F (x : ℂ) = F ((w : ℝ) : ℂ) := hgx
    _ = beukersHComplex a (x : ℂ) := by
      rw [hS]
      exact hS2

/-- **the real-axis bridge (interval form)**: with `ρ < R0²` the descent
covers all of `(0, ρ)`, so the `ρ`-extension `g(z) = F(ρ−z)` equals the
holomorphic companion `Hℂ` at **every** real point `x` of the interval
`(0, ρ)` — the two anchored ends of the continuation agree along the whole
continuation path -/
lemma beukers_apéry_rho_extension_interval (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z) :
    ∀ x : ℝ, 0 < x → x < beukersRho a →
      beukersApéryRhoExt a F (x : ℂ) = beukersHComplex a (x : ℂ) := by
  intro x hx0 hxρ
  apply beukers_apéry_rho_extension_interval_gen a ha hFdesc hxρ
  · have hw : beukersRho a - x < beukersRho a := by linarith
    exact lt_trans hw hR0big
  · have hw : beukersRho a - x < beukersRho a := by linarith
    exact lt_trans hw (beukers_rho_lt_two_sqrt a ha)

/-- **the two-sided real-axis bridge**: under `ρ < R0²` the equality
`g(↑x) = Hℂ(↑x)` of the interval bridge extends to a whole real
neighbourhood of `0` (both `x > 0` and `x < 0` near `0` — for negative `x`
the point `w = ρ − x > ρ` is still inside the coordinate discs because
`R0² > ρ` leaves room) -/
lemma beukers_apéry_rho_extension_realAxis_eventually (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z) :
    ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), beukersApéryRhoExt a F (x : ℂ) = beukersHComplex a (x : ℂ) := by
  have hρ0 : 0 < beukersRho a := beukers_rho_pos a ha
  have hset1 : ({x : ℝ | x < beukersRho a} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Iio.mem_nhds (by simpa using hρ0)
  have hset2 : Set.Ioi (beukersRho a - (R0 : ℝ) ^ 2) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Ioi.mem_nhds (by simpa using (sub_neg.mpr hR0big))
  have hset3 : Set.Ioi (beukersRho a - 2 * Real.sqrt (a ^ 2 - 1)) ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Ioi.mem_nhds (by simpa using (sub_neg.mpr (beukers_rho_lt_two_sqrt a ha)))
  filter_upwards [hset1, hset2, hset3] with x hx1 hx2 hx3
  have hx2' : beukersRho a - (R0 : ℝ) ^ 2 < x := by simpa using hx2
  have hx3' : beukersRho a - 2 * Real.sqrt (a ^ 2 - 1) < x := by simpa using hx3
  have hc1 : beukersRho a - x < (R0 : ℝ) ^ 2 := by linarith
  have hc2 : beukersRho a - x < 2 * Real.sqrt (a ^ 2 - 1) := by linarith
  exact beukers_apéry_rho_extension_interval_gen a ha hFdesc hx1 hc1 hc2


/-! ### A6 — holomorphy of the `ρ`-extension at `0` and the germ equality

The analytic continuation through `ρ` is now upgraded to the power-series
language at `0`.  The `ρ`-extension `g(z) = F(ρ−z)` is holomorphic at `0`
(`beukersApéryRhoExt_analyticAt_zero`, from the holomorphy of `F` on the
`w`-disc `|w| < R0²` containing `ρ`) and — with `ρ < R0²` — agrees with the
holomorphic companion `Hℂ` at every real point of `(0, ρ)` (the interval
bridge `beukers_apéry_rho_extension_interval`).  Both functions being
holomorphic at `0`, the *principle of isolated zeros* (`AnalyticAt`'s
dichotomy `eventually_eq_zero_or_eventually_ne_zero`) forces their germs at
`0` to agree on a whole complex neighbourhood
(`beukers_apéry_g_eq_HComplex_eventually`).  Consequently the power series
of `Hℂ` at `0` — `Σ (v_n − η_a·u_n)·zⁿ`, `beukersHComplex_hasSum_series` —
also represents `g` near `0` (`beukers_apéry_g_hasSum_series`), and `g` has
that formal power series at `0` (`beukers_apéry_g_hasFPowerSeriesAt`).

Since `g` is holomorphic on the *whole* disc `|z| < R0² − ρ` (strictly
bigger than `1` when `R0² > ρ + 1`, `beukersApéryRhoExt_analyticAt_of_ball`),
the formal power series `Σ (v_n − η_a·u_n)·zⁿ` has radius of convergence at
least `min(R0² − ρ, …) > 1/a` — the overconvergence of the companion series
through the singularity.  The Cauchy coefficient bounds
(`|v_n − η_a·u_n| ≤ C·r^{−n}` for `r > 1/a`) and the Apéry-limit
identification are assembled from this in the next section.
-/

/-- the `ρ`-extension `g(z) = F(ρ−z)` is holomorphic at `0` when `F` is
holomorphic on the `w`-disc of radius `R0²` containing `ρ` (`ρ < R0²`) -/
lemma beukersApéryRhoExt_analyticAt_zero (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) :
    AnalyticAt ℂ (beukersApéryRhoExt a F) 0 := by
  have hρ0 : 0 ≤ beukersRho a := le_of_lt (beukers_rho_pos a ha)
  have hFρ : AnalyticAt ℂ F (((beukersRho a : ℝ) : ℂ)) := by
    apply hF.analyticAt_of_mem
    rw [mem_eball_zero_iff]
    have hn : ‖((beukersRho a : ℝ) : ℂ)‖ < (R0 : ℝ) ^ 2 := by
      have hnorm : ‖((beukersRho a : ℝ) : ℂ)‖ = beukersRho a := by
        simp [abs_of_nonneg hρ0]
      rw [hnorm]
      exact hR0big
    have hlt : (‖((beukersRho a : ℝ) : ℂ)‖₊ : ℝ≥0∞) < ((R0 ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      apply ENNReal.coe_lt_coe.mpr
      exact_mod_cast hn
    simpa [ENNReal.coe_pow, enorm] using hlt
  have hZ : AnalyticAt ℂ (fun z : ℂ => ((beukersRho a : ℝ) : ℂ) - z) 0 := by
    fun_prop
  have hF0 : AnalyticAt ℂ F (((beukersRho a : ℝ) : ℂ) - 0) := by
    simpa using hFρ
  have hcomp : AnalyticAt ℂ (F ∘ (fun z : ℂ => ((beukersRho a : ℝ) : ℂ) - z)) 0 :=
    hF0.comp (x := 0) hZ
  change AnalyticAt ℂ (fun z : ℂ => F (((beukersRho a : ℝ) : ℂ) - z)) 0
  exact hcomp

/-- `g(z) = F(ρ−z)` is holomorphic at every `z` of the unit disc around `0`
when `F` is holomorphic on the `w`-disc of radius `R0² > ρ + 1` (then
`‖ρ−z‖ < ρ + ‖z‖ < ρ + 1 < R0²`) -/
lemma beukersApéryRhoExt_analyticAt_of_unitBall (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a + 1 < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (beukersApéryRhoExt a F) z := by
  have hρ0 : 0 ≤ beukersRho a := le_of_lt (beukers_rho_pos a ha)
  let y : ℂ := ((beukersRho a : ℝ) : ℂ) - z
  have hyn : ‖y‖ < (R0 : ℝ) ^ 2 := by
    have hnorm_le : ‖y‖ ≤ ‖((beukersRho a : ℝ) : ℂ)‖ + ‖z‖ := by
      dsimp [y]
      exact norm_sub_le (((beukersRho a : ℝ) : ℂ)) z
    have hρn : ‖((beukersRho a : ℝ) : ℂ)‖ = beukersRho a := by
      simp [abs_of_nonneg hρ0]
    calc
      ‖y‖ ≤ ‖((beukersRho a : ℝ) : ℂ)‖ + ‖z‖ := hnorm_le
      _ = beukersRho a + ‖z‖ := by rw [hρn]
      _ < (R0 : ℝ) ^ 2 := by
        have hz1 : ‖z‖ < 1 := hz
        linarith
  have hFy : AnalyticAt ℂ F y := by
    apply hF.analyticAt_of_mem
    rw [mem_eball_zero_iff]
    have hlt : (‖y‖₊ : ℝ≥0∞) < ((R0 ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      apply ENNReal.coe_lt_coe.mpr
      exact_mod_cast hyn
    simpa [ENNReal.coe_pow, enorm] using hlt
  have hZ : AnalyticAt ℂ (fun w : ℂ => ((beukersRho a : ℝ) : ℂ) - w) z := by
    fun_prop
  have hF0 : AnalyticAt ℂ F (((beukersRho a : ℝ) : ℂ) - z) := by
    simpa [y] using hFy
  have hcomp : AnalyticAt ℂ (F ∘ (fun w : ℂ => ((beukersRho a : ℝ) : ℂ) - w)) z :=
    hF0.comp (x := z) hZ
  change AnalyticAt ℂ (fun w : ℂ => F (((beukersRho a : ℝ) : ℂ) - w)) z
  exact hcomp

/-- **the germ equality**: the `ρ`-extension `g = F(ρ−z)` and the holomorphic
companion `Hℂ` agree on a whole complex neighbourhood of `0` (their germs at
`0` coincide: the two functions are holomorphic at `0` and agree at the real
points of `(0, ρ)`, which accumulate at `0` — principle of isolated zeros) -/
lemma beukers_apéry_g_eq_HComplex_eventually (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2)))
    (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z) :
    ∀ᶠ z in 𝓝 (0 : ℂ), beukersApéryRhoExt a F z = beukersHComplex a z := by
  have hfan : AnalyticAt ℂ (beukersApéryRhoExt a F) 0 :=
    beukersApéryRhoExt_analyticAt_zero a ha hR0big hF
  have hHan : AnalyticAt ℂ (beukersHComplex a) 0 := beukersHComplex_analyticAt_zero a ha
  have hhn : AnalyticAt ℂ (fun z : ℂ => beukersApéryRhoExt a F z - beukersHComplex a z) 0 :=
    hfan.sub hHan
  rcases hhn.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · -- hz : eventually (difference = 0) → f = Hℂ
    filter_upwards [hz] with z hz0
    have heq : beukersApéryRhoExt a F z = beukersHComplex a z := sub_eq_zero.mp hz0
    exact heq
  · -- hnz : difference ≠ 0 on a punctured neighbourhood of 0 — but it vanishes
    -- at the real points ↑x, 0 < x < ρ, arbitrarily close to 0
    exfalso
    rw [eventually_nhdsWithin_iff] at hnz
    rw [Metric.eventually_nhds_iff] at hnz
    rcases hnz with ⟨δ, hδ, hδ'⟩
    have hρ0 : 0 < beukersRho a := beukers_rho_pos a ha
    let ε : ℝ := min (beukersRho a) (δ / 2)
    have hε0 : 0 < ε := by
      dsimp [ε]
      exact lt_min hρ0 (by linarith)
    let x : ℝ := ε / 2
    have hx0 : 0 < x := by
      dsimp [x]
      positivity
    have hεle_ρ : ε ≤ beukersRho a := by
      dsimp [ε]
      exact min_le_left (beukersRho a) (δ / 2)
    have hεle_δ2 : ε ≤ δ / 2 := by
      dsimp [ε]
      exact min_le_right (beukersRho a) (δ / 2)
    have hxρ : x < beukersRho a := by
      dsimp [x]
      linarith
    have hxδ : ‖(x : ℂ)‖ < δ := by
      have hxδ' : x < δ := by
        dsimp [x]
        linarith
      have hxnonneg : 0 ≤ x := le_of_lt hx0
      simpa [RCLike.norm_ofReal (K := ℂ), abs_of_nonneg hxnonneg]
    have hneq : (x : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hx0)
    have hhz : (fun z : ℂ => beukersApéryRhoExt a F z - beukersHComplex a z) (x : ℂ) ≠ 0 := by
      exact hδ' (by simpa [dist_zero_right] using hxδ) hneq
    have hbridge := beukers_apéry_rho_extension_interval a ha hR0big hFdesc x hx0 hxρ
    have hzero : (fun z : ℂ => beukersApéryRhoExt a F z - beukersHComplex a z) (x : ℂ) = 0 := by
      dsimp
      rw [hbridge]
      ring
    exact hhz hzero

/-- **the power series of `g` near `0`**: the `ρ`-extension `g = F(ρ−z)` is
represented near `0` by the companion series
`Σ (v_n(a) − η_a·u_n(a))·zⁿ` (the series of `Hℂ` at `0`, transported to `g`
through the germ equality) -/
lemma beukers_apéry_g_hasSum_series (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2)))
    (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ) * z ^ n)
        (beukersApéryRhoExt a F z) := by
  have hge := beukers_apéry_g_eq_HComplex_eventually a ha hR0big hF hFdesc
  filter_upwards [beukersHComplex_hasSum_series a ha, hge] with z hzH hzEq
  have hz : HasSum (fun n : ℕ =>
      ((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ) * z ^ n)
        (beukersApéryRhoExt a F z) := by
    simpa [hzEq] using hzH
  exact hz

/-- **the formal power series of `g` at `0`**: `g` has the formal power
series `ofScalars ℂ (v_n − η_a·u_n)` at `0` (the analytic meaning of the
overconvergence: the companion series converges to `g` near `0`) -/
lemma beukers_apéry_g_hasFPowerSeriesAt (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0big : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2)))
    (hFdesc : ∀ z : ℂ, ‖z‖ < (R0 : ℝ) → F (z ^ 2) = beukersG0 a ha z) :
    HasFPowerSeriesAt (beukersApéryRhoExt a F)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ => ((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [beukers_apéry_g_hasSum_series a ha hR0big hF hFdesc] with z hz
  simpa [zero_add] using (hz.congr_fun (by
    intro n
    simp [mul_comm]))


/-- `ρ_a + 1 < 2·√(a²−1)` for `a ≥ 3` — the `w = u²`-disc of radius
`2√(a²−1)` around `ρ_a` covers the unit disc around `0` (this is the margin
that makes the `ρ`-extension holomorphic on the unit disc) -/
lemma beukers_rho_add_one_lt_two_sqrt (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a + 1 < 2 * Real.sqrt (a ^ 2 - 1) := by
  have hLstrict : a - 1 < Real.sqrt (a ^ 2 - 1) := by
    have hsq_lt : (a - 1) ^ 2 < a ^ 2 - 1 := by nlinarith
    have hsqrt_lt : Real.sqrt ((a - 1) ^ 2) < Real.sqrt (a ^ 2 - 1) :=
      Real.sqrt_lt_sqrt (sq_nonneg (a - 1)) hsq_lt
    have hroot : Real.sqrt ((a - 1) ^ 2) = a - 1 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      linarith
    rwa [hroot] at hsqrt_lt
  have hmain : a + 1 < 3 * Real.sqrt (a ^ 2 - 1) := by
    have h1 : a + 1 < 3 * (a - 1) := by nlinarith
    have h2 : 3 * (a - 1) < 3 * Real.sqrt (a ^ 2 - 1) := by
      exact mul_lt_mul_of_pos_left hLstrict (by norm_num)
    exact lt_trans h1 h2
  dsimp [beukersRho]
  linarith

/-- **existence of the descent radius**: for `a ≥ 3` there is a radius
`R0 < R_u = √(2√(a²−1))` of the `u`-coordinate disc with `ρ_a + 1 < R0²` —
so the descended `F` (from `beukersG0_descends_sq_onBall`) is holomorphic on
the `w = u²`-disc of radius `R0² > ρ_a + 1`, which makes the `ρ`-extension
`g(z) = F(ρ_a − z)` holomorphic on the whole unit disc around `0` -/
lemma beukers_exists_descend_R0 (a : ℝ) (ha : 3 ≤ a) :
    ∃ R0 : ℝ≥0, (R0 : ℝ) < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1)) ∧
      beukersRho a + 1 < (R0 : ℝ) ^ 2 := by
  let mid : ℝ := (beukersRho a + 1 + 2 * Real.sqrt (a ^ 2 - 1)) / 2
  have hρ0 : 0 ≤ beukersRho a := le_of_lt (beukers_rho_pos a ha)
  have hmid_gt : beukersRho a + 1 < mid := by
    dsimp [mid]
    have h : beukersRho a + 1 < 2 * Real.sqrt (a ^ 2 - 1) :=
      beukers_rho_add_one_lt_two_sqrt a ha
    linarith
  have hmid_lt : mid < 2 * Real.sqrt (a ^ 2 - 1) := by
    dsimp [mid]
    have h : beukersRho a + 1 < 2 * Real.sqrt (a ^ 2 - 1) :=
      beukers_rho_add_one_lt_two_sqrt a ha
    linarith
  have hmid_nonneg : 0 ≤ mid := by
    have hc0 : 0 ≤ Real.sqrt (a ^ 2 - 1) := Real.sqrt_nonneg _
    dsimp [mid]
    nlinarith
  refine ⟨⟨Real.sqrt mid, Real.sqrt_nonneg mid⟩, ?_, ?_⟩
  · change Real.sqrt mid < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))
    exact Real.sqrt_lt_sqrt hmid_nonneg hmid_lt
  · have hsq : (Real.sqrt mid) ^ 2 = mid := Real.sq_sqrt hmid_nonneg
    have hR0 : ((⟨Real.sqrt mid, Real.sqrt_nonneg mid⟩ : ℝ≥0) : ℝ) = Real.sqrt mid := rfl
    calc
      beukersRho a + 1 < mid := hmid_gt
      _ = (Real.sqrt mid) ^ 2 := hsq.symm
      _ = ((⟨Real.sqrt mid, Real.sqrt_nonneg mid⟩ : ℝ≥0) : ℝ) ^ 2 := by rw [hR0]


/-! ### A6 — assembly: the geometric coefficient bound of the companion series

This is the pay-off of the continuation.  With the descended `F` of the
brick-A4 ball form at a radius `R0` with `ρ_a + 1 < R0²`
(`beukers_exists_descend_R0` — possible because `ρ_a + 1 < 2√(a²−1)`), the
`ρ`-extension `g(z) = F(ρ−z)` is holomorphic on the whole unit disc
(`beukersApéryRhoExt_analyticAt_of_unitBall`), equals the companion `Hℂ`
near `0` (the germ equality), and hence carries the formal power series
`Σ (v_n − η_a·u_n)·zⁿ` (`beukers_apéry_g_hasFPowerSeriesAt`) all the way to
the unit disc.  For every circle radius `r` with `1/a < r < 1` the *Cauchy
estimate* (`Commons.Analysis.Complex.cauchy_coeff_bound`) then gives the
geometric coefficient bound

`‖(v_n(a) − η_a·u_n(a) : ℂ)‖ ≤ C / rⁿ`   for all `n`,

i.e. **`beukers_apéry_coeff_growth`**: the companion coefficients decay at a
geometric rate `r^{−n}` with `r > 1/a`.  Since `u_n(a) ≥ aⁿ`
(`beukersU_lower_bound`) this makes `(v_n − η_a·u_n)/u_n = O((a·r)^{−n}) → 0`
— the engine of the Apéry-limit identification (next section).
-/

/-- **the geometric coefficient bound (A6-main)**: there are `C > 0` and
`r > 1/a` with `‖(v_n(a) − η_a·u_n(a) : ℂ)‖ ≤ C / rⁿ` for every `n` — the
companion power series `Σ(v_n − η_a·u_n)·zⁿ` overconverges past the
singularity `ρ_a` with coefficient decay at a rate `r^{−n}`, `r > 1/a` -/
theorem beukers_apéry_coeff_growth (a : ℝ) (ha : 3 ≤ a) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ (1 : ℝ) / a < r ∧
      ∀ n : ℕ, ‖(((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ))‖ ≤ C / r ^ n := by
  classical
  -- 1. choose the descent radius R0 with ρ + 1 < R0² and R0 < R_u
  rcases beukers_exists_descend_R0 a ha with ⟨R0, hR0lt, hR0big⟩
  have hR0pos : (0 : ℝ) < (R0 : ℝ) := by
    have hρ1 : 0 < beukersRho a + 1 := by linarith [beukers_rho_pos a ha]
    nlinarith [sq_nonneg (R0 : ℝ)]
  have hR0posNN : 0 < R0 := by exact_mod_cast hR0pos
  rcases beukersG0_descends_sq_onBall a ha R0 hR0posNN hR0lt with ⟨F, q, hF, hF0, hFdesc⟩
  let g : ℂ → ℂ := beukersApéryRhoExt a F
  -- 2. the Cauchy circle radius r := (1/a + 1)/2, with 1/a < r < 1
  let rv : ℝ := (1 / a + 1) / 2
  have ha0 : 0 < a := by linarith
  have hr0 : 0 < rv := by
    dsimp [rv]
    positivity
  have hr_gt : (1 : ℝ) / a < rv := by
    dsimp [rv]
    field_simp [ha0.ne']
    nlinarith
  have hr1 : rv < 1 := by
    dsimp [rv]
    have h : (1 : ℝ) / a < 1 := by
      field_simp [ha0.ne']
      nlinarith
    linarith
  have hR0big_ρ : beukersRho a < (R0 : ℝ) ^ 2 := by
    have h : beukersRho a < beukersRho a + 1 := by linarith
    exact lt_trans h hR0big
  -- 3. g is holomorphic on the unit disc (hence differentiable there)
  have hd_ball : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa [dist_zero_right] using hz
    have hz_an := beukersApéryRhoExt_analyticAt_of_unitBall a ha hR0big hF hz1
    have hg_an : AnalyticAt ℂ g z := by simpa [g] using hz_an
    exact hg_an.differentiableAt.differentiableWithinAt
  have hd_cl : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) rv) := by
    exact hd_ball.mono (Metric.closedBall_subset_ball hr1)
  -- 4. bound M of ‖g‖ on the circle of radius rv
  have hcont_sphere : ContinuousOn g (Metric.sphere (0 : ℂ) rv) := by
    exact hd_ball.continuousOn.mono (by
      intro z hz
      have hzr : ‖z‖ = rv := by simpa [dist_zero_right] using hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
  have hK : IsCompact (Metric.sphere (0 : ℂ) rv) := isCompact_sphere (0 : ℂ) rv
  have hKne : (Metric.sphere (0 : ℂ) rv).Nonempty := by
    refine ⟨(rv : ℂ), ?_⟩
    have hrv0 : 0 ≤ rv := le_of_lt hr0
    rw [Metric.mem_sphere, dist_zero_right]
    simp [abs_of_nonneg hrv0]
  have hnormCont : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.sphere (0 : ℂ) rv) :=
    continuous_norm.comp_continuousOn hcont_sphere
  rcases hK.exists_isMaxOn hKne hnormCont with ⟨am, haK, hmax⟩
  let M : ℝ := ‖g am‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg (g am)
  have hM : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) rv → ‖g z‖ ≤ M := by
    intro z hz
    exact hmax hz
  -- 5. the power series at 0 of g and its OnBall-representation on the circle
  let cseq : ℕ → ℂ := fun n => ((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ)
  let p0 : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ cseq
  have hFPS0 : HasFPowerSeriesAt g p0 0 := by
    have h1 := beukers_apéry_g_hasFPowerSeriesAt a ha hR0big_ρ hF hFdesc
    simpa [g, p0, cseq] using h1
  have hrv0 : 0 ≤ rv := le_of_lt hr0
  let R : ℝ≥0 := ⟨rv, hrv0⟩
  have hR0nn : 0 < R := by exact_mod_cast hr0
  have hd_clR : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) R) := hd_cl
  have hp_ball : HasFPowerSeriesOnBall g (cauchyPowerSeries g (0 : ℂ) R) (0 : ℂ) R :=
    DifferentiableOn.hasFPowerSeriesOnBall hd_clR hR0nn
  have hEqSeries : cauchyPowerSeries g (0 : ℂ) R = p0 := by
    exact hp_ball.hasFPowerSeriesAt.eq_formalMultilinearSeries hFPS0
  have hp0ball : HasFPowerSeriesOnBall g p0 (0 : ℂ) R := by
    simpa [hEqSeries] using hp_ball
  have hp_final : HasFPowerSeriesOnBall g p0 (0 : ℂ) (ENNReal.ofReal rv) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hrv0]
    exact hp0ball
  -- 6. Cauchy estimate
  refine ⟨M + 1, rv, by nlinarith [hM0], hr0, hr_gt, ?_⟩
  intro n
  have hcau := Commons.Analysis.Complex.cauchy_coeff_bound (f := g) (ρ := rv) (M := M)
    hr0 hM hd_cl hp_final n
  have hpcoeff : p0 n (fun _ : Fin n => (1 : ℂ)) =
      ((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ) := by
    dsimp [p0, cseq]
    simp
  calc
    ‖((beukersVR a n - beukersEta a * beukersUR a n : ℝ) : ℂ)‖
        = ‖p0 n (fun _ : Fin n => (1 : ℂ))‖ := by rw [hpcoeff]
    _ ≤ M / rv ^ n := hcau
    _ ≤ (M + 1) / rv ^ n := by
      have hpow : 0 < rv ^ n := pow_pos hr0 n
      have hinv : 0 ≤ (rv ^ n)⁻¹ := le_of_lt (inv_pos.mpr hpow)
      have hle : M ≤ M + 1 := by linarith
      calc
        M / rv ^ n = M * (rv ^ n)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (M + 1) * (rv ^ n)⁻¹ := mul_le_mul_of_nonneg_right hle hinv
        _ = (M + 1) / rv ^ n := by rw [div_eq_mul_inv]


/-! ### A7 — the Apéry limit: `lim v_N(a)/u_N(a) = η_a`

The coefficient bound of the previous section
(`beukers_apéry_coeff_growth`: `|v_n(a) − η_a·u_n(a)| ≤ C·r^{−n}` with
`r > 1/a`) together with the geometric lower bound `u_n(a) ≥ aⁿ`
(`beukersUR_lower_bound`, real-parameter version of
`beukersU_lower_bound`) yields

`|v_n(a)/u_n(a) − η_a| ≤ C·(a·r)^{−n} → 0`  (`a·r > 1`),

i.e. **`beukers_apéry_limit`**: the Apéry ratio of the companion series
converges to `η_a = ½·log((a+1)/(a−1))` (paper eq. (beukerslimit)).  For a
rational parameter `ã ≥ 3` the same limit is restated with the rational
coefficients `beukersU`/`beukersV` (`beukers_apéry_limit_rat`, via the
cast bridges `beukersUR_eq_cast`/`beukersVR_eq_cast`).
-/

/-- real-parameter geometric growth of the ratios: `u_{n+1} ≥ a·uₙ` for
`a ≥ 1` (real version of `beukersU_ratio`) -/
lemma beukersUR_ratio (a : ℝ) (ha : 1 ≤ a) : ∀ n : ℕ, beukersUR a (n + 1) ≥ a * beukersUR a n := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hasq : 1 ≤ a * a := by nlinarith
  have hmain : ∀ n, beukersUR a (n + 1) ≥ a * beukersUR a n ∧ 0 ≤ beukersUR a n := by
    intro n
    induction n with
    | zero =>
        constructor <;> simp [beukersUR]
    | succ m ih =>
        constructor
        · rcases ih with ⟨hge, hnn⟩
          have hrec := beukersUR_step a m
          have hdiff : ((m : ℝ) + 2) * (beukersUR a (m + 2) - a * beukersUR a (m + 1))
              = ((m : ℝ) + 1) * (a * beukersUR a (m + 1) - beukersUR a m) := by
            nlinarith [hrec]
          have haum1 : a * beukersUR a (m + 1) ≥ a * (a * beukersUR a m) :=
            mul_le_mul_of_nonneg_left hge ha0
          have haum2 : a * (a * beukersUR a m) ≥ beukersUR a m := by
            have hc : 0 ≤ (a * a - 1) * beukersUR a m := mul_nonneg (sub_nonneg.mpr hasq) hnn
            nlinarith
          have hRHS : 0 ≤ a * beukersUR a (m + 1) - beukersUR a m := by
            nlinarith
          have hm2 : 0 < (m : ℝ) + 2 := by positivity
          have hm1 : 0 ≤ (m : ℝ) + 1 := by positivity
          have hnonneg : 0 ≤ beukersUR a (m + 2) - a * beukersUR a (m + 1) := by
            have hmul : 0 ≤ ((m : ℝ) + 2) * (beukersUR a (m + 2) - a * beukersUR a (m + 1)) := by
              rw [hdiff]
              exact mul_nonneg hm1 hRHS
            rw [mul_comm] at hmul
            exact nonneg_of_mul_nonneg_left hmul hm2
          linarith
        · rcases ih with ⟨hge, hnn⟩
          exact le_trans (mul_nonneg ha0 hnn) hge
  exact fun n => (hmain n).1

/-- real-parameter positivity of the coefficients for `a ≥ 1` (real version
of `beukersU_pos`) -/
lemma beukersUR_pos (a : ℝ) (ha : 1 ≤ a) (n : ℕ) : 0 < beukersUR a n := by
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  induction n with
  | zero => simp [beukersUR]
  | succ m ih =>
      exact lt_of_lt_of_le (mul_pos hapos ih) (beukersUR_ratio a ha m)

/-- real-parameter lower bound `uₙ ≥ aⁿ` for `a ≥ 1` (real version of
`beukersU_lower_bound`) -/
lemma beukersUR_lower_bound (a : ℝ) (ha : 1 ≤ a) : ∀ n : ℕ, a ^ n ≤ beukersUR a n := by
  intro n
  induction n with
  | zero => simp [beukersUR]
  | succ m ih =>
      have h1 := beukersUR_ratio a ha m
      have h2 : a * beukersUR a m ≥ a * a ^ m :=
        mul_le_mul_of_nonneg_left ih (le_trans zero_le_one ha)
      have h3 : a * a ^ m = a ^ (m + 1) := by
        rw [pow_succ, mul_comm]
      nlinarith

/-- **the Apéry limit (A7-main, real parameter)**: for real `a ≥ 3` the ratio
`v_N(a)/u_N(a)` of the companion coefficients converges to
`η_a = ½·log((a+1)/(a−1))` as `N → ∞` (paper eq. (beukerslimit)) -/
theorem beukers_apéry_limit (a : ℝ) (ha : 3 ≤ a) :
    Tendsto (fun n : ℕ => beukersVR a n / beukersUR a n) atTop (𝓝 (beukersEta a)) := by
  classical
  rcases beukers_apéry_coeff_growth a ha with ⟨C, r, hC, hr0, hgr, hcoeff⟩
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hupos : ∀ n : ℕ, 0 < beukersUR a n := beukersUR_pos a ha1
  have hlb : ∀ n : ℕ, a ^ n ≤ beukersUR a n := beukersUR_lower_bound a ha1
  have hcoeffabs : ∀ n : ℕ,
      |beukersVR a n - beukersEta a * beukersUR a n| ≤ C / r ^ n := by
    intro n
    have h1 := hcoeff n
    have hcast (t : ℝ) : ‖((t : ℝ) : ℂ)‖ = |t| := by simp
    rw [hcast] at h1
    exact h1
  have har : 1 < a * r := by
    have h1div : (1 : ℝ) < r * a := (div_lt_iff₀ ha0).mp hgr
    nlinarith
  let q : ℝ := 1 / (a * r)
  have har0 : 0 < a * r := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one har0).2 har
  have hpow0 : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hCq0 : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow0)
  -- pointwise bound: |v_n/u_n − η| ≤ C · qⁿ
  have hbound : ∀ n : ℕ, |beukersVR a n / beukersUR a n - beukersEta a| ≤ C * q ^ n := by
    intro n
    let d : ℝ := beukersVR a n - beukersEta a * beukersUR a n
    have hdabs : |d| ≤ C / r ^ n := by
      simpa [d] using hcoeffabs n
    have hun : 0 < beukersUR a n := hupos n
    have hapn : 0 < a ^ n := pow_pos ha0 n
    have hdn : (beukersVR a n / beukersUR a n - beukersEta a : ℝ) = d / beukersUR a n := by
      dsimp [d]
      field_simp [ne_of_gt hun]
    have hstep1 : |d| / beukersUR a n ≤ |d| / a ^ n := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hiu : (beukersUR a n)⁻¹ ≤ (a ^ n)⁻¹ := by
        simpa using (one_div_le_one_div_of_le hapn (hlb n))
      exact mul_le_mul_of_nonneg_left hiu (abs_nonneg d)
    have hstep2 : |d| / a ^ n ≤ (C / r ^ n) / a ^ n := by
      exact div_le_div_of_nonneg_right hdabs (le_of_lt hapn)
    have hstep3 : (C / r ^ n) / a ^ n = C * q ^ n := by
      dsimp [q]
      rw [one_div_pow]
      rw [mul_pow]
      field_simp [ne_of_gt (pow_pos hr0 n), ne_of_gt hapn]
    calc
      |beukersVR a n / beukersUR a n - beukersEta a| = |d / beukersUR a n| := by rw [hdn]
      _ = |d| / beukersUR a n := by
        rw [abs_div]
        rw [abs_of_nonneg (le_of_lt hun)]
      _ ≤ |d| / a ^ n := hstep1
      _ ≤ (C / r ^ n) / a ^ n := hstep2
      _ = C * q ^ n := hstep3
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hCq0
    (fun n => norm_nonneg (beukersVR a n / beukersUR a n - beukersEta a))
    (fun n => by simpa using hbound n)

/-- **the Apéry limit with rational parameter** (the CDT application): for a
rational `ã ≥ 3` the ratio `v_N(ã)/u_N(ã)` of the rational companion
coefficients converges to `η_{ã} = ½·log((ã+1)/(ã−1))` (the real-parameter
limit `beukers_apéry_limit` restated through the cast bridges
`beukersVR_eq_cast`/`beukersUR_eq_cast`) -/
theorem beukers_apéry_limit_rat (ã : ℚ) (ha : 3 ≤ ã) :
    Tendsto (fun n : ℕ => ((beukersV ã n : ℝ) / (beukersU ã n : ℝ))) atTop
      (𝓝 (beukersEta (ã : ℝ))) := by
  have h : 3 ≤ (ã : ℝ) := by exact_mod_cast ha
  have hreal := beukers_apéry_limit (ã : ℝ) h
  simpa [beukersVR_eq_cast, beukersUR_eq_cast] using hreal




/-- the shifted coefficient form of `v_{n+1}` as a range sum:
`v_{n+1} = Σ_{k=0}^{n} u_{n−k}·u_k/(k+1)` -/
lemma beukersVR_succ_range (a : ℝ) (n : ℕ) :
    beukersVR a (n + 1) =
      ∑ k ∈ Finset.range (n + 1), beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ)) := by
  apply Finset.sum_bij (fun j hj => j - 1)
  · intro j hj
    have hj2 : j ≤ n + 1 := (Finset.mem_Icc.mp hj).2
    simp [Finset.mem_range]
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    have h₁ : 1 ≤ j₁ := (Finset.mem_Icc.mp hj₁).1
    have h₂ : 1 ≤ j₂ := (Finset.mem_Icc.mp hj₂).1
    omega
  · intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    refine ⟨k + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h₁ : n + 1 - j = n - (j - 1) := by omega
    have hc : (((j - 1) + 1 : ℕ) : ℝ) = (j : ℝ) := by
      congr 1
      exact Nat.sub_add_cancel hj1
    have hden : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      calc
        (j : ℝ) = (((j - 1) + 1 : ℕ) : ℝ) := hc.symm
        _ = ((j - 1 : ℕ) : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    calc
      beukersUR a (n + 1 - j) * (beukersUR a (j - 1) / ↑j)
          = beukersUR a (n - (j - 1)) * (beukersUR a (j - 1) / ↑j) := by rw [h₁]
      _ = beukersUR a (n - (j - 1)) * (beukersUR a (j - 1) / (((j - 1 : ℕ) : ℝ) + 1)) := by
            rw [hden]

/-- upper geometric growth of the companion coefficients `v_n(a)` -/
lemma beukersVR_growth (a : ℝ) (ha : 3 ≤ a) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ n : ℕ, |beukersVR a n| ≤ C * ρ ^ n := by
  rcases beukersUR_growth a ha with ⟨C, ρ, hC, hρ, hu⟩
  let ρ₀ : ℝ := max ρ 1
  have hC0 : 0 ≤ C := le_of_lt hC
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hρ₀ge1 : 1 ≤ ρ₀ := by
    dsimp [ρ₀]
    exact le_max_right ρ 1
  have hρle : ρ ≤ ρ₀ := by
    dsimp [ρ₀]
    exact le_max_left ρ 1
  have hCρ : ∀ m : ℕ, 0 ≤ C * ρ ^ m := fun m => mul_nonneg hC0 (pow_nonneg hρ0 m)
  have hC2 : 0 ≤ C * C := mul_nonneg hC0 hC0
  have hρ₀0 : 0 ≤ ρ₀ := le_of_lt (lt_of_lt_of_le hρ hρle)
  have hk2 : ∀ k : ℕ, (k : ℝ) ≤ (2 : ℝ) ^ k := by
    intro k
    have hk2n : k ≤ 2 ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
          have hz : 0 < 2 ^ k := by positivity
          have hone : 1 ≤ 2 ^ k := by omega
          calc
            k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
            _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hone _
            _ = 2 ^ (k + 1) := by
                  rw [pow_succ]
                  ring
    exact_mod_cast hk2n
  refine ⟨C * C, 2 * ρ₀, by positivity, by positivity, ?_⟩
  intro n
  cases n with
  | zero =>
      have hv0 : beukersVR a 0 = 0 := by
        dsimp [beukersVR]
        simp
      simp [hv0, pow_zero]
      exact mul_self_nonneg C
  | succ n =>
      have hper : ∀ k ∈ Finset.range (n + 1),
          |beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ))| ≤ C * ρ ^ (n - k) * (C * ρ ^ k) := by
        intro k hk
        have hk1r : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
        have hkpos : 0 < (k + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos k)
        have h1 : |beukersUR a (n - k)| ≤ C * ρ ^ (n - k) := hu (n - k)
        have h2 : |beukersUR a k / (k + 1 : ℝ)| ≤ C * ρ ^ k := by
          calc
            |beukersUR a k / (k + 1 : ℝ)| = |beukersUR a k| / (k + 1 : ℝ) := by
                  rw [abs_div]
                  rw [abs_of_pos hkpos]
            _ ≤ |beukersUR a k| := div_le_self (abs_nonneg _) hk1r
            _ ≤ C * ρ ^ k := hu k
        calc
          |beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ))|
              ≤ |beukersUR a (n - k)| * |beukersUR a k / (k + 1 : ℝ)| := by
                  rw [abs_mul]
          _ ≤ (C * ρ ^ (n - k)) * (C * ρ ^ k) := mul_le_mul h1 h2 (abs_nonneg _) (hCρ (n - k))
      have hmain : |beukersVR a (n + 1)| ≤ (C * C) * ρ ^ n * (n + 1 : ℝ) := by
        calc
          |beukersVR a (n + 1)|
              = |∑ k ∈ Finset.range (n + 1), beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ))| := by
                  rw [beukersVR_succ_range]
          _ ≤ ∑ k ∈ Finset.range (n + 1), |beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ))| := by
                  exact (Finset.abs_sum_le_sum_abs (s := Finset.range (n + 1))
                    (fun k => beukersUR a (n - k) * (beukersUR a k / (k + 1 : ℝ))))
          _ ≤ ∑ k ∈ Finset.range (n + 1), C * ρ ^ (n - k) * (C * ρ ^ k) := Finset.sum_le_sum hper
          _ = ∑ k ∈ Finset.range (n + 1), (C * C) * ρ ^ n := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hk' : k < n + 1 := Finset.mem_range.mp hk
                  have hsub : (n - k) + k = n := by omega
                  calc
                    C * ρ ^ (n - k) * (C * ρ ^ k) = (C * C) * (ρ ^ (n - k) * ρ ^ k) := by ring
                    _ = (C * C) * ρ ^ n := by
                          rw [← pow_add]
                          rw [hsub]
          _ = (C * C) * ρ ^ n * (n + 1 : ℝ) := by
                  rw [Finset.sum_const]
                  simp
                  ring
      have htail : ρ₀ ^ n * (n + 1 : ℝ) ≤ (2 * ρ₀) ^ (n + 1) := by
        calc
          ρ₀ ^ n * (n + 1 : ℝ) ≤ ρ₀ ^ n * ((2 : ℝ) ^ (n + 1) * ρ₀) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ρ₀ ^ n)
                calc
                  (n + 1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
                        simpa [Nat.cast_add] using hk2 (n + 1)
                  _ ≤ (2 : ℝ) ^ (n + 1) * ρ₀ := by
                        exact le_mul_of_one_le_right (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1)) hρ₀ge1
          _ = (2 * ρ₀) ^ (n + 1) := by
                rw [mul_pow, pow_succ']
                ring
      calc
        |beukersVR a (n + 1)| ≤ (C * C) * ρ ^ n * (n + 1 : ℝ) := hmain
        _ ≤ (C * C) * ρ₀ ^ n * (n + 1 : ℝ) := by
              have hp : (C * C) * ρ ^ n ≤ (C * C) * ρ₀ ^ n := by
                exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρle n) hC2
              have hnn : 0 ≤ (n + 1 : ℝ) := by positivity
              exact mul_le_mul_of_nonneg_right hp hnn
        _ = (C * C) * (ρ₀ ^ n * (n + 1 : ℝ)) := by ring
        _ ≤ (C * C) * (2 * ρ₀) ^ (n + 1) := by
              exact mul_le_mul_of_nonneg_left htail hC2


end Submission.CDT
