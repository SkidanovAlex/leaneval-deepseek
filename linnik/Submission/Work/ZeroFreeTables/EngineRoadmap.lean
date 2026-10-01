/-
# ZeroFreeTables — EngineRoadmap

**Read this before proving any of the `Prop`s of `Engine.lean` / `HBProps.lean`.**
It records, for each input `Prop` of `Main.Area3_of_engine_P3`, the paper's own
section, the infrastructure in this workspace that implements its ingredients, and
the intended proof route.  Nothing here is a theorem: it is the map.

Notation: **[HB]** = Heath-Brown, *Zero-free regions for Dirichlet L-functions, and
the least prime in an arithmetic progression*, PLMS 64 (1992) 265–338 (page numbers
of the author's version, `dev/hb.txt` in this directory); **[X]** = Xylouris,
arXiv:0906.2749.  All the `Prop`s are stated with the §6 minimality
`API.IsMin1WideAt 10` (`IsMin1` plus minimality of `λ₁` over the strip `|Im| ≤ 10`
for every non-principal character) — HB (6.1)–(6.2) with the rectangle of height 10;
the round-2 contract supplies it.

## Common infrastructure already proved in this workspace (do not reprove)

* `Commons.NumberTheory.Linnik.logDeriv_pf_identity`, `partialFraction_*` — the
  partial-fraction decomposition of `L'/L` (HB (4.7), (4.8), (5.6)).
* `Commons.NumberTheory.Linnik.lemma3_1`, `lemma3_1_sigma_ge_one` — **HB Lemma 3.1**
  with `φ = 1/3` (the Burgess input `LBound13` of AREA 1), in the form used by §8.
* `Commons.NumberTheory.Linnik.completedL_zeroCount`, `completedL_zero_strip`,
  `zeroSum_invSq_bound`, `nearSum_bound`, `lorentzian_zeroSum` — the zero counting and
  the near/far zero-sum bounds of HB §3/§5.
* `Commons.NumberTheory.Linnik.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt` — the
  von Mangoldt series of `L'/L` on `Re s > 1`.
* `ZeroFreeTables.P3.DefsL` — `SigmaP3L` (HB (8.4) with free scale `L` **and the
  coefficient-correct weight** `u(y) = α + α²y + (1/3)α³y²`, whose Laplace transform is
  `P₃(α/z)`), `hbWL`, `HbCombinationL` (HB (9.1)'s left side), `pdiv`, `P3NearSumL`
  (HB's near-zero sum over `Re P₃(α/((s-u)L))`), `InvNearSum` (the near-zero sum of
  `1/(s-u)` of HB Lemma 3.1), `LogDerivHyp` (the hypothesis of HB Lemma 3.1).
  Beware `P3.Defs.SigmaP3`/`HbCombination`: their `y²`-coefficient is `2/3`, i.e. the
  functional of `X+X²+(4/3)X³`; they are kept only because `Pointwise91` is stated for
  them.  **Use the `L` versions.**
* `ZeroFreeTables.P3.WLBase` — the `L`-analogues of the summand books of
  `Pointwise91` (`hbTermL`, `hbRawL`, `hbSummandL`, `hbRawSumL`) and the bridge lemmas
  `SigmaP3L_eq_hbRawL`, `hbRawL_eq_hbTermL`, `hbWL_nonneg`, `hbWL_abs_le`,
  `hbRawL_abs_le`.
* `ZeroFreeTables.P3.Pointwise91` — `Pointwise91 : 0 ≤ HbCombination ...`, the
  *pointwise* HB (9.1) for the `2/3`-weight combination (proved, ~200 lines, with
  `HbKernelIdentity`, `hbSummand_nonneg`, absolute-convergence bookkeeping).  The
  `L`-version is **proved** as `P9.HbCombinationL_nonneg` (`P9/` is the sub-chapter
  of the keystone, built while this roadmap was written).
* `ZeroFreeTables.P3.HbKernelIdentity` — the algebraic kernel identity
  `(K²+½)(1+Re z₀) + K((z₁/z₀).re + 2z₁.re + (z₁z₀).re) + ¼((z₁²/z₀).re + 2(z₁²).re + (z₁²z₀).re)
   = (1+Re z₀)(K+Re z₁)²` on the unit circle.
* `ZeroFreeTables.P3.SideConditions` — `side913`: HB (9.9)–(9.12) from `cond913`.
* `ZeroFreeTables.P3.P3Bounds` (`P3Bounds`), `P3.CaseC_D` (`CaseC_D`) — the
  `Re P₃` comparisons that give `A ≥ 0` (HB (9.8) with (9.9)/(9.11)): `φ(a,b,c) =
  Re P₃(a/(b+ic))` monotone comparisons and the `(K²+3/4, 2K, K)`/`(2K, ½, ½)`
  rescalings of HB (9.11), (9.12).
* `ZeroFreeTables.P3.CompletedDerivPF` — the partial-fraction expansion of the `k`-th
  derivative of `L'/L` (HB §8's `(-1)^k/k! L^{-k}(L'/L)^{(k-1)} = -L^{-k}Σ_{near}(s-ρ)^{-k}
  + O(L)`, with the far part made explicit).
* `ZeroFreeTables.P3.LogRatioBounds`, `Summand_norm_le`, `annulusKDSum_le`,
  `annulusMass_count_le`, `dyadicAnnulusKernel_le`, `dyadicLogSeries_le`,
  `cofactorIteratedDeriv_le`, `SummableVonMangoldtLogPow`, `SummableSigmaTerm` — the
  elementary size bounds and summability that the near/far split needs.
* `ZeroFreeTables.HB4_1.hb_lemma4_1` — HB Lemma 4.1 (maximum principle on `Re z ≥ 0`).
* `ZeroFreeTables.P3Pos` — HB (4.11) for `P₃`, sharp, and the dropping rule
  `Re P₃(w) ≥ 0` for `|w|² ≤ Re w`.
* `ZeroFreeTables.TrigPolyPos`, `ksum_trigPoly_pointwise`, `ksum_trigPoly_nonneg` —
  the Chebyshev/trigonometric positivity transfer (HB (9.15)–(9.16), Lemma 10.3).
* `ZeroFreeTables.testFn7_2` (with `testFn72_defs`, `tf72Fc_*`) — **HB Lemma 7.2's**
  optimal test function as a `TestFn` (`x₀ = 2/λ`, `f 0 = 16λ/15`, `F 0 = 8/9`,
  `F(−λ) = 8/5`), i.e. the rational test function of the `F`-method.
* `ZeroFreeTables.TestFn_F_*`, `HBProps.HBLemma6_3/6_4`, `Engine.HBLemma8_5/8_7/9_2/9_3`
  — the `F`-method interface (HB §§6, 8, 9).
* `ZeroFreeTables.Table8CertPrinted`/`Table8CertExtPrinted` — the rational certificate
  for HB Table 8 (all 21 printed entries); `Lemma10_3Cert`, `Lemma10_3CertZero` — the
  rational core of HB Lemma 10.3 at `ε = 1/1000` and `ε = 0`.

## The `Prop`s, one by one

### `Engine.HBLemma9_1` (the keystone; HB §9, pp. 49–52)
`0 ≤ (K²+½){P₃((a+λ₁)/a) − P₃((a+λ₁)/(a+λ₀))} − 2K P₃(1) + (a+λ₁)(ψ+ε)`, i.e. `ineq913`,
for a pair `ρ₁ ≠ ρ₀` of zeros of `χ₁` with `χ₁` or `ρ₁` complex, under (9.12).
Route: (i) **HB (9.1)** — the pointwise inequality `0 ≤ χ₀(n)(1+Re z₀)(K+Re z₁)²`
summed: `Pointwise91` proves it for the `2/3`-weight; restate it for `HbCombinationL`
(`WLBase` has the summands and the bridges); (ii) **HB (8.4)/(8.5)** — the identity
`Σ(s,χ) = L⁻¹Σ_n Λ(n)Re(χ(n)n^{-s})u(log n/L)` on `Re s > 1` and its derivative form
(finite algebra from the von Mangoldt series of `L'/L`), then the near/far split via
`CompletedDerivPF`: `Σ(s,χ) ≤ −P3NearSumL(s) + (a+λ₁)(φ/2+ε)` for `q ≥ q₀`; (iii) the
eight-term bounds (9.2)–(9.7) (each is (ii) applied at one of the eight points of (9.1),
with the *near* zeros identified using the `IsMin1WideAt 10` minimality and HB Lemma 3.1
(`LogDerivHyp`) for the `k=1` term); (iv) feed (9.2)–(9.7) into (9.1) to get (9.8),
`0 ≤ (K²+½){...} − 2KP₃(1) − A + (a+λ₁)(ψ+ε)` with `A` the `A913` of `P3.Defs`;
(v) `A ≥ 0` from `side913` (HB (9.9)) + the `Re P₃` comparisons of `P3Bounds`/`CaseC_D`
(HB's "we handle A just as in the proof of Lemma 8.3"); (vi) rearrange to `ineq913`.
The three cases `ord χ₁ ∉ {2,3}` / `χ₁³ = χ₀` / `χ₁² = χ₀` change `ψ` and the form of
`A` (HB (9.10), (9.11), (9.12)); `ψ = (1/6)(K²+3K+3/2)` is `Engine.psi13`.

### `Engine.HBLemma10_3_engine` (HB §10, pp. 56–66)
`0 ≤ p1014 (λ₁/(6/7)) ε` under `λ₃ ≤ 6/7`, where the three `λ`'s are the successive
minima.  Route: HB (9.15)–(9.17): the Chen-type inequality
`(3+10cos θ)²(9+10cos θ)² ≥ 0` expanded as `14379 + 24480cos θ + 14900cos2θ + 6000cos3θ + 1250cos4θ`
(i.e. a Chebyshev polynomial with non-negative coefficients — `TrigPolyPos` /
`ksum_trigPoly_nonneg` apply verbatim), the positive combination
`0 ≤ 14379K(β,χ₀) + 24480K(β+iγ₁,χ₁) + ...` (HB (9.16)), and the near/far bounds as in
`HBLemma9_1` with `a = 3λ₃`, `λ₁ = δλ₃`.  The rational core
(`∀ δ ∈ [0,1], p1014 δ (1/1000) < 0`) is `Lemma10_3Cert`; the assembly
`HB10_3_conclusion_of_engine` (proved) already turns the engine `Prop` plus the
certificate into `HB10_3_conclusion`, so the whole remaining content is the §10
inequality itself.

### `HBProps.HBTheorem1` (HB Theorem 1 / §3)
For `λ₁ < 0.348`: `χ₁` is real, `ρ₁` is real and simple, and every *other* zero of the
working region has `λ ≥ 0.348`.  Route: the classical "at most one exceptional zero"
argument of HB §3 (`K(β,χ)` positivity with the weights of (4.9)/(4.12)) — the
`P₃`-type weight is best (`P3Pos`); the near/far machinery as above.

### `HBProps.XYLemma3_8` ([X] Lemma 3.8, Xylouris §3.6)
`χ₁² = 1 ∧ ρ₁.im ≠ 0 → λ₁ ≥ 0.628`.  This is an external input (Xylouris's thesis);
its proof is not in this workspace.  If it is to be proved, it needs Xylouris's
`l1`-estimates for the real case (his Lemma 3.8 uses the Deuring–Heilbronn repulsion
plus his own computations).

### The table `Prop`s and their certificates
`HBTable4` (real `χ₁, ρ₁`, `λ₀`), `HBTable7`, `HBTable7phi3` (real, `λ₂`), `HBTable9`
(complex, `λ_j` for `j = 2,3`), `HBLemma9_4` (Table 10 in all cases), `HBRepZero`
(the repeated-zero case).  Each has the Table-8 shape: an *analytic* inequality
(HB Lemmas 6.2–6.4, 8.5, 8.7, 8.8, 9.2, 9.3 — the `F`-method `Prop`s of `Engine.lean`)
plus a *certificate* at the tabulated rationals.  The certificates are what is missing
for 4/7/9/10: they need (i) the explicit test functions of HB §7 (Lemma 7.2's is
`testFn7_2`; **Lemma 7.1's θ-family is the one Tables 2, 3, 9, 10, 11 come from and is
not yet constructed**) and (ii) rigorous bounds on `F = ∫ e^{-zt} f` at the tabulated
points (interval arithmetic).  `HBLemma8_4` and `HBLemma8_8` (HB §8) use Lemma 7.2's
function together with the elementary integral bounds of HB §8.1–8.3
(`2F(−λ₀) − 2F(λ₁−λ₀) = ∫ f(t)e^{λ₀t}(1−e^{−λ₁t})dt ≤ λ₀⁻³(x₀λ₀e^{x₀λ} − ...)`), which are
*elementary* once `testFn7_2`'s explicit `f` (`tf72f`) is available.
-/
