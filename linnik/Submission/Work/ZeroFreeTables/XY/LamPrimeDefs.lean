/-
# ZeroFreeTables/XY/LamPrimeDefs

Interface for the `λ'`-estimate `Work.ZeroFreeTables.XY.LamPrimeLower` (the order-2 slice
of Xylouris's `λ'`-section, Table 3).

The lemma `LamPrimeLower` says: if `χ₁` is real (`χ₁² = 1`), `ρ₁` is a non-real zero which
minimises `λ` over the strip `|Im| ≤ 10`, and `λ₁ = λ(ρ₁) ≤ 0.628`, then **every** other zero
`u ≠ ρ₁, ρ̄₁` of `χ₁` with `|Im u| ≤ 10` has `λ(u) ≥ 1`.

The proof is the `ord χ₁ = 2` case of Xylouris's *Nebenfall* inequality (his §"λ'-Abschätzungen",
Fall 2): starting from the pointwise positivity

  `0 ≤ χ₀(n) (1 + Re{χ₁(n) n^{-iγ'}}) (k + Re{χ₁(n) n^{-iγ₁}})²`

(summed with `Λ(n) n^{-β₁} f(log n / log q)`) and using HB Lemma 5.2 in its "working form"
(the extended form with the choice `A₂ ⊆ {zeros with Re ρ ≤ Re s}`, HB §6) at the eight points
`β₁`, `β₁ ± iγ'`, `β₁ + i(γ₁ ∓ γ')`, `β₁ + iγ₁`, `β₁ + i(2γ₁ ∓ γ')`, `β₁ + 2iγ₁`, one obtains
(with `k = 1`, and where `sup G`, `sup H` are the two suprema below)

  `0 ≤ (3/2)(F(-λ₁) - F(λ'-λ₁)) - 2F(0) + (f(0)/6)·4 + 2·sup G + sup H + ε`.

The two supremum functions are `Gfun`/`Hfun` here; both are bounded by `1/25` for the test
function `xyT` and `λ ≤ 0.628` (they are in fact `≤ 0`, the maximum being a limit as `t → ∞`).

Everything is stated for the concrete test function `xyT = tf72T (4/3)` of `XYDefs`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Commons.NumberTheory.Linnik.lemma5_3
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem_ne
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- `G_k(λ,t) = k·Re F(-λ+it) - (k²+3/4)·Re F(it)`, the first supremum function of the
order-2 `Nebenfall` inequality. -/
def Gfun (k lam t : ℝ) : ℝ := k * xyRe (-lam) t - (k ^ 2 + 3 / 4) * xyRe 0 t

/-- `H_k(λ,t) = (1/2)·Re F(-λ+it) - 2k·Re F(it)`, the second supremum function. -/
def Hfun (k lam t : ℝ) : ℝ := (1 / 2) * xyRe (-lam) t - 2 * k * xyRe 0 t

/-- `Gλ(λ,t) = Re F(-λ+it) - (3/2)·Re F(it)`: the first supremum function of the order-2
`Nebenfall` inequality when the imaginary-axis compensation comes only from the **low** points
(`β₁ ± iγ'`, `β₁ ± iγ₁`) — the configuration in which the retained zeros all lie in balls whose
zeros are covered by `IsMin1WideAt 10`. -/
def GfunLow (lam t : ℝ) : ℝ := xyRe (-lam) t - (3 / 2) * xyRe 0 t

/-- `Hλ(λ,t) = (1/2)·Re F(-λ+it) - 2·Re F(it)`, the second supremum function in the same
configuration. -/
def HfunLow (lam t : ℝ) : ℝ := (1 / 2) * xyRe (-lam) t - 2 * xyRe 0 t

end Work.ZeroFreeTables.XY

/-!

## Route notes for the two analytic/numeric inputs

### `LamPrimeSup` (the two suprema)

Write `f = xyT.f = tf72f (4/3)` (HB Lemma 7.2's optimal test function, support `[0, 3/2]`,
`x₀ = 3/2`) and `F = xyF`.  The two quantities are

  `Gfun 1 λ t = Re ∫₀^{x₀} f(s)(e^{λs} - 7/4) e^{-its} ds`,
  `Hfun 1 λ t = Re ∫₀^{x₀} f(s)(e^{λs}/2 - 2) e^{-its} ds`.

*Numerically both suprema are `≤ 0`* (attained only as the limit `t → ∞`), so the constants
`1/25` have a large margin.  Two structural facts help:

* (Convolution structure) `tf72conv_eq_f` gives `f = g * g` with `g = tf72g (4/3)`
  (`g(x) = (4/3)(1 - (16/9)x²)` on `|x| ≤ 3/4`, even, non-negative).  Hence
  `∫_ℝ f(s) e^{-zs} ds = (∫_ℝ g(x)e^{-zx}dx)²`, and for `z = it` this gives
  `F(it) = (∫_ℝ g(x)cos(tx)dx)²/2 = 2 (∫₀^{γ} g cos(t·))² ≥ 0` (Condition 2 on the axis).
  With `A(z) := ∫_ℝ g(x) e^{-zx}dx` one has, for every `λ` and `t`,
  `2 Re F(-λ+it) = A(it-λ)² - 2 Re F(λ+it)` (`F(z) + F(-z) = A(z)²` for our `f`), and
  `Re F(λ+it) ≥ 0` by Condition 2 (`tf72Fc_re_nonneg`), whence
  `2 Re F(-λ+it) ≤ A(it-λ)² = (P² - Q²)` with `P = ∫_ℝ g e^{λx}cos(tx)`,
  `Q = ∫_ℝ g e^{λx}sin(tx)`.  Splitting `P = 2(C + E)`, `Q = 2B` with
  `C = ∫₀^γ g cos(t·)`, `E = ∫₀^γ g (cosh(λ·)-1) cos(t·)`, `B = ∫₀^γ g sinh(λ·) sin(t·)`
  gives `Gfun 1 λ t ≤ -3/2 C² + 4CE + 2E² - 2B² + S` and `Hfun 1 λ t ≤ -3C² + 2CE + E² - B² + S/2`,
  where `S = ∫₀^{x₀} f(s) sinh(λs) cos(ts) ds` and `|S| ≤ S₀ = (F(-λ) - F(λ))/2`,
  `|E| ≤ E₀ = ∫₀^γ g(cosh(λ·)-1)`, `|C| ≤ C₀ = ∫₀^γ g = 2/3`.
  These crude bounds give `~0.25` and `~0.12` — not quite enough; the `S`-term is what needs
  a sharper treatment (or the whole supremum an explicit numerical/interval argument on the
  closed form of `F`, cf. Xylouris §2 "Abschätzung gewisser Suprema", grid `Δt = 0.004`,
  `t ≤ x₁ = 15`, plus the integration-by-parts decay for `t ≥ x₁`).

### `LamPrimeNebenfall`

Start from `0 ≤ χ₀(n)(1 + Re{χ₁(n)n^{-iγ'}})(k + Re{χ₁(n)n^{-iγ₁}})²` (with `k = 1`),
multiply by `Λ(n) n^{-β₁} f(log n / log q)` and sum: this is the eight-term combination of
Xylouris's `λ'`-section (Fall 2, `ord χ₁ = 2`, so `χ₁² = 1`).  Bound each term by
`Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_param_imprim` (imprimitive characters
included, `χ ≠ 1`, `L = log q`) resp. `Commons.NumberTheory.Linnik.lemma5_3` (the principal
character), in the *working form* with the choice `A₂` of retained zeros; the dropped zeros
have `Re ρ ≤ Re s`, and `Re F ≥ 0` there (`tf72Fc_re_nonneg`).  The two extra zeros-retentions
at the points `β₁ + i(2γ₁ ∓ γ')` and `β₁ - iγ₁` sharpen the coefficients to `k²+3/4` and `2k`
(cf. `Gfun`/`Hfun`); those points are at height up to `30`, but the zeros retained there are
`ρ₁` (height `|Im ρ₁| ≤ 10`), so `IsMin1WideAt 10` supplies the needed `Re ρ ≤ Re s`.  (The
*working form* of HB Lemma 5.2 — allowing an arbitrary `A₂ ⊆ {zeros with Re ρ ≤ Re s}` rather
than the `δ`-window of `lemma5_2_of_logDeriv_bound_param_imprim` — is the one additional
ingredient; `explicitFormula_chi_gen_wide` + `lemma3_1` + the dropping rule is the direct
route.  Note `le_windowSum_of_mem_ne` and `le_windowSum_of_mem` handle the "keep/replace a
single window zero" bookkeeping.)
-/

/-!
### Available machinery for `LamPrimeNebenfall` (as of the current workspace)

* `Submission.Work.ZeroFreeTables.XY.KsumTwoWorking` — **the working form of HB Lemma 5.2
  (Xylouris Lemma 3.4) with two retained zeros that need NOT lie in the `δ`-window**
  (`KsumTwoWorking`); it bounds the `K`-sum by `-L(ord ρ·Re F((s-ρ)L) + ord ρ'·Re F((s-ρ')L))
  + f(0)(c+ε)L`, exactly the form the eight-term combination below needs.  Its hypotheses
  `ord ρ ≤ 10`, `|Re((s-ρ)L)| ≤ 1`, and `∀ u, divisor u ≠ 0 → ‖1+i·Im s - u‖ ≤ δ → s.re < u.re
  → u = ρ ∨ u = ρ'` are what `IsMin1WideAt 10` supplies (via the contrapositive
  `λ(u) < λ₁ → 10 < |u.im|`).
* `Submission.Work.ZeroFreeTables.XY.LamPrimeData` / `LamPrimeAux` — the decomposition of
  `xyRe (-λ) t` into `Cc, Ec, Bc, Sc` and the identity `2 Re F(-λ+it) = A(it-λ)² - 2 Re F(λ+it)`
  (`xyRe_neg_lam_eq`, `Ac_it_sub_re/im`), together with `Gfun_eq`/`Hfun_eq` in `LamPrimeSup`.
* `Submission.Work.ZeroFreeTables.XY.LamPrimeSup` — `Gfun 1 λ t ≤ 1/25`, `Hfun 1 λ t ≤ 1/25`
  for `0 ≤ λ ≤ 628/1000` (proved).
-/

/-!
#### The one missing ingredient, precisely

`KsumTwoWorking` / `KsumChiTwoZerosWindow` retain zeros that are **to the right** of the
evaluation point (`s.re < ρ.re`) or inside the `δ`-window.  The eight-term `Nebenfall`
combination needs the opposite: the retained zeros `ρ' , ρ₁, ρ̄₁` all satisfy
`Re u ≤ Re s = β₁` (they are zeros of `χ₁` with `λ(u) ≥ λ₁`), and apart from `ρ'` they are
**outside** the window.  The required lemma is therefore

> `WindowSumLeft` (working form of HB Lemma 5.2, `A₂` to the left): for `A₂` a finite set of
> zeros of `χ` in the ball `closedBall 0 (|s.im|+2)`, all with `Re u ≤ Re s`, and with
> `L52Hyp χ c ε δ`,
> `K(s,χ) ≤ -L · Σ_{u ∈ A₂} ord(u) · Re F((s-u)L) + f(0)·(c+ε)·L`.

It is *provable from the machinery already in the workspace*: start from
`explicitFormula_chi_gen_wide` (`K + L·Σ_full[F((s-u)L) - f(0)/((s-u)L)] + f(0)(L'/L)(s) = o(L)`)
and `L52Hyp` (`-(L'/L)(s) + Σ_{near} ord·Re(1/(s-u)) ≤ cL`).  The zeros split three ways:

* **near-window** zeros: combine their two sums (`F` and `1/(s-u)`) exactly as in the proof of
  `KsumChiTwoZerosWindow`, and keep only the ones in `A₂` — dropping a near zero with
  `Re u ≤ Re s` is legitimate because its `F`-term is `≥ 0` (Condition 2, `tf72Fc_re_nonneg`);
* **far** zeros (outside the window) with `Re u ≤ Re s`: their combined contribution
  `-L·Re F((s-u)L) + f(0)·Re(1/(s-u))` is `≤ f(0)·Re(1/(s-u))` (the `F`-term is `≥ 0`), and
  `Σ_far |1/(s-u)|` is bounded by an absolute constant (`far_zero_invSq_sum`), so retaining all
  of them costs `O(1)` — absorbed in `f(0)·ε·L` for `q ≥ q₀(ε)`;
* **zeros with `Re u > Re s`** (i.e. `λ(u) < λ(s)`): these cannot be dropped, and they are
  excluded by the hypothesis that every zero of `χ` with `λ(u) < λ(s)` has `|Im u| > 10`
  (the contrapositive of `IsMin1WideAt 10`, applied at `s` with `λ(s) = λ₁`), together with
  `|Im s| + 2 ≤ 10` for the points used (the retained-zero points of the eight-term combination
  are `β₁ ± iγ'`, `β₁ ± iγ₁`, and `β₁ ± i(2γ₁∓γ')`; at the last two the *retained* zero `ρ₁` is
  at height `≤ 10` and any zero in the ball with `|Im| ≤ 10` has `λ ≥ λ₁`).

For the last point one may also use the symmetric form: only the heights `|Im s| ≤ 8` points
need the retention, and the two `(1/4)`-coefficient terms can be dropped (losing `1/4·F(0)`)
if necessary.
-/

/-!

#### Corrected route, after two prover refutations (see the child reports)

Two independent provers *refuted* the first drafts and their diagnoses fix the shape:

1. **`KsumLeftWorking` must bound `#A`.**  With `A` = *all* ball zeros the conclusion is false
   (the ball sum of `1/(s-u)` is `≈ (1/2)log q` by Riemann–von Mangoldt, while `L52Hyp` controls
   only the `δ`-window part).  Add `A.card ≤ 10`.
2. **The `Nebenfall` inequality must carry the *actual* suprema, not free constants.**
   With `c₁,c₂` only *lower-bounded* by the suprema the hypothesis is satisfiable by
   `c₁ = c₂ = 0`, and then the conclusion is *equivalent* to the statement that no admissible
   configuration exists — i.e. to `LamPrimeLower` itself.  Write the conclusion with
   `sSup (Set.range (GfunLow λ₁ ·))` / `sSup (Set.range (HfunLow λ₁ ·))`.
3. **Retain only low-height zeros.**  The F-method's eight points have heights up to
   `2|γ₁| + |γ'| ≤ 30`; a ball zero at height in `(10, 30]` with `λ < λ₁` is *not* excluded by
   `IsMin1WideAt 10` and would cost `O(L)`.  Using only the four low points `β₁ ± iγ'`,
   `β₁ ± iγ₁` for the *retentions* (the compensations `Re F(i(μ'∓μ₁))`, `Re F(2iμ₁)` come from
   retaining `ρ₁`, `ρ̄₁` at their own heights, which are in the window) and the *crude* bound
   `K ≤ (f(0)/2)φL` for the four high points gives the inequality

   `0 ≤ (3/2)(F(-λ₁) - F(λ_u - λ₁)) - 2F(0) + (f(0)/6)·4 + 2·sSup(range (GfunLow λ₁ ·)) + sSup(range (HfunLow λ₁ ·)) + ε`,

   and the retained zeros then all lie in balls `closedBall 0 (|Im s| + 2)` with
   `|Im s| ≤ |γ'| ≤ 10` (resp. `≤ |γ₁| ≤ 10`), so every ball zero has `|Im| ≤ 12`; the
   remaining gap is exactly the minimality at height `12` instead of `10`.

Numerically (`λ₁ = 0.628`, test function `xyT`): `sup GfunLow = -4·10⁻⁵ ≤ 0` and
`sup HfunLow = -2·10⁻⁵ ≤ 0`, while the margin at `λ₁ = 628/1000` is
`(3/2)(F(-0.628) - F(0.372)) - 2F(0) + (f(0)/6)·4 = -0.2651`.
-/
