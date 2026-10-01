/-
# ZeroFreeTables — Engine.lean

The analytic engine of AREA 3 in the shape in which the paper's tables are read,
and the exact statement of each of Heath-Brown's inequalities as a `Prop`.

Source: **[HB]** Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
least prime in an arithmetic progression*, PLMS **64** (1992) 265–338 (page
references to the author's version).

## The `P₃` method (HB §4, §§8–10)

HB Lemma 4.1 (the maximum principle) applied to `p(1/(1+iy))` with `p` one of the
polynomials (4.12) turns the positivity of `1 + Re(χ(n)n^{-iγ})` into the
inequality `0 ≤ Σ_ρ Re p((a+λ₁)/((s−ρ)𝓛))`, which is the "power-sum / Turán-type"
engine of §§8–10.  The polynomial used for `λ₀` (Table 8) and `λ₃` (Lemma 10.3) is
the third one of (4.12), `P₃(X) = X + X² + X³`; its numerical content is *rational*
and is verified in `Table8.lean` and `Lemma10_3.lean`.

## The `F` method (HB §§5–7, 9)

The optimal test functions of §7 (Lemmas 7.1–7.3) give the inequalities of §6 and
of the second half of §9, which are stated here in terms of the Laplace transform
`F` of a test function satisfying HB's Conditions 1 and 2 (`TestFn`).  Their
numerical content is transcendental (Tables 7, 9, 10, 11).

## Status

Every `Prop` below is a faithful, unabbreviated restatement of the paper's claim
in the vocabulary of `Work.LinnikContract`.  Proofs of the engine inequalities
need the derivative version of HB Lemma 5.2 (the `P₃`-functional analogue of the
proved `Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound`); they are the
open work of this area.  What *is* complete here: the definitions, the exact
statements, and the full rational verification of the two `P₃`-based results
(`HBLemma9_1` → Table 8, `HBLemma10_3` → `λ₃ ≥ 6/7`).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## HB's polynomial `P₃` and the data of HB Lemma 9.1 -/

/-- HB's polynomial (4.12), the third one, `P₃(X) = X + X² + (2/3)X³`, at real
arguments.  (The coefficient `2/3` is what makes condition (4.11),
`Re P₃(1/(1+iy)) ≥ 0`, hold — indeed `Re P₃(1/(1+iy)) = (8/3)/(1+y²)³`; with the
coefficient `1` it fails, e.g. at `y = 3`.  HB's (4.12) reads
`X, X + X², X + X² + (2/3)X³, (2/5)X + X² + X³ + (4/5)X⁴`.) -/
def P3R (x : ℝ) : ℝ := x + x ^ 2 + (2/3) * x ^ 3

/-- HB's polynomial (4.12), the third one, `P₃(X) = X + X² + (2/3)X³`, at complex
arguments. -/
def P3 (z : ℂ) : ℂ := z + z ^ 2 + (2/3) * z ^ 3

/-- HB's choice `K = 0.775 + 0.15 λ₁` for Table 8. -/
def Kaff (lam₁ : ℝ) : ℝ := 775/1000 + 15/100 * lam₁

/-- The constant `ψ = (φ/2)(K² + 3K + 3/2)` of HB (9.13) with `φ = 1/3`.

The total weight of the `(a+λ₁)(φ/2 + ε)` terms in HB (9.1)–(9.7) is
`K² + 3K + 3/2`.  With `ψ` read as this coefficient and HB's polynomial
`P₃(X) = X + X² + (2/3)X³`, the inequality (9.13) reproduces HB's Table 8: all
twenty-one entries are derived in `Table8Derive.lean` from the certificates
`Table8Cert`/`Table8CertExt` with explicit witnesses (`t8certRows`,
`t8certRowsExt`).  With the printed `ψ = (3/2)(K²+3K+φ/2)` the inequality is
vacuous at every tabulated point and the table cannot be produced. -/
def psi13 (K : ℝ) : ℝ := (1/6) * (K ^ 2 + 3 * K + 3/2)

/-- HB's `K₀ = min(K + 3/(4K), 4K)` of Lemma 9.1. -/
def Kond (K : ℝ) : ℝ := min (K + 3 / (4 * K)) (4 * K)

/-- The side condition of HB Lemma 9.1, `K₀(a+λ₁)^{-3} + (a+λ₀)^{-3} ≥ a^{-3}`
(with the divisions explicit; the denominators are positive in every use). -/
def cond913 (lam₁ lam₀ a K : ℝ) : Prop :=
  Kond K / (a + lam₁) ^ 3 + 1 / (a + lam₀) ^ 3 ≥ 1 / a ^ 3

/-- The left hand side of HB (9.13) (with `φ = 1/3`), *without* the `ε` term. -/
def p913 (lam₁ lam₀ a K : ℝ) : ℝ :=
  (K ^ 2 + 1/2) * (P3R ((a + lam₁) / a) - P3R ((a + lam₁) / (a + lam₀)))
    - 2 * K * P3R 1 + (a + lam₁) * psi13 K

/-- HB (9.13): `(K² + 1/2){P₃((a+λ₁)/a) − P₃((a+λ₁)/(a+λ₀))} − 2K P₃(1) + (a+λ₁)(ψ+ε) ≥ 0`. -/
def ineq913 (lam₁ lam₀ a K ε : ℝ) : Prop := 0 ≤ p913 lam₁ lam₀ a K + (a + lam₁) * ε

/-- **HB Lemma 9.1** (p. 52), engine form.  For positive `a`, `K`, `ε` there is
`q₀` such that for `q ≥ q₀`, if `χ₁`(mod `q`) has two **distinct** zeros `ρ₁ ≠ ρ₀`
in the working region with `χ₁` or `ρ₁` complex, and if
`K₀(a+λ₁)⁻³ + (a+λ₀)⁻³ ≥ a⁻³`, then `ineq913 (λ(ρ₁)) (λ(ρ₀)) a K ε` holds.

Proof roadmap (for whoever proves this `Prop`): write `Σ(s,χ)` for HB's (8.4)
functional with `p = P₃` (§4), use the derivative form of the partial-fraction
expansion of `L'/L` (HB (4.7), (4.8); the workspace has `logDeriv_pf_identity`
and the `partialFraction_*` family) to turn `Σ` into the sum over zeros, handle
the `k = 1` term with the *proved* `Commons.NumberTheory.Linnik.lemma3_1` (HB
Lemma 3.1, `φ = 1/3`), and drop the remaining zero terms with the maximum
principle (HB Lemma 4.1) — those terms are `Re P₃((a+λ₁)/((s-ρ)𝓛)) ≥ 0` whenever
`Re ρ ≤ Re s`, which is where `IsMin1WideAt 10 χ₁ ρ₁` is used (and *not* merely the
working-region minimality `IsMin1`: the window of (9.1) reaches `|Im u| ≤ 3 + δ`).  The bookkeeping (9.1)–(9.8)
then gives (9.13).

The exclusion `χ₁² = 1 → ρ₀ ≠ conj ρ₁` is HB's convention in the real case (the
same one used by `Lam0Bound`): when `χ₁` is real and `ρ₁` complex, `ρ₀ = conj ρ₁`
has `λ₀ = λ₁` and the inequality genuinely fails (a colleague's numbers: `λ₁ = λ₀ =
0.63`, `a = 2`, `K = Kaff 0.63` satisfy the side condition while `p913 < 0`), so it
must be excluded.  The tables' `λ₀` is the maximum of `λ` over the zeros *other*
than `ρ₁` and `conj ρ₁`.

The case `ρ₀ = ρ₁` (a repeated zero) is *not* covered by this inequality: the
§9 derivation is run at the two distinct points `σ+iγ⁰` and `σ+iγ₁` and in the
repeated case both the `P₃(1)` term and the weights change (the conclusion at
`λ₀ = λ₁` genuinely fails, so the restriction is necessary).  The repeated case
is the subject of `HBRepZero` in `HBProps.lean`. -/
def HBLemma9_1 : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₁ ≠ ρ₀ → (χ₁ ^ 2 = 1 → ρ₀ ≠ starRingEnd ℂ ρ₁) →
      cond913 (lamOf q ρ₁) (lamOf q ρ₀) a K →
      ineq913 (lamOf q ρ₁) (lamOf q ρ₀) a K ε

/-! ## HB Lemma 10.3 (`λ₃ ≥ 6/7`) -/

/-- HB (10.14) at `a = 3λ₃`, `λ₁ = δλ₃`, `λ₂ = λ₃ = 6/7`:
`P₃((3+δ)/3) − P₃(1) − 2P₃((3+δ)/4) + (3+δ)(3λ₃/2 + ε)`, i.e. with `λ₃ = 6/7`,
`P₃((3+δ)/3) − P₃(1) − 2P₃((3+δ)/4) + (3+δ)(9/14 + ε)`.  HB's contradiction is
`p1014 δ ε < 0` for `0 ≤ δ ≤ 1`. -/
def p1014 (δ ε : ℝ) : ℝ :=
  P3R ((3 + δ)/3) - P3R 1 - 2 * P3R ((3 + δ)/4) + (3 + δ) * (9/14 + ε)

/-- **HB (10.14)** (p. 66) in its *setting*: `ρ₁`, `ρ₂`, `ρ₃` are zeros of
non-principal characters **numbered as in HB §6** — `ρ₁` realises the smallest `λ`
(`IsMin1WideAt 10`), `(χ₂,ρ₂)` is a zero outside the pairs `χ₁^{±1}` with `ρ₂` minimising
`λ` among those, and `(χ₃,ρ₃)` is a zero outside `{χ₁^{±1}, χ₂^{±1}}` with `ρ₃`
minimising `λ` there — with `λ₂ ≤ λ₃ ≤ 6/7`.  Then the inequality (10.14) at
`a = 3λ₃ = 18/7`, `λ₁ = δλ₃` holds: `0 ≤ p1014 (λ₁/(6/7)) ε`.

**The exclusions `χ₂ ∉ {χ₁^{±1}}`, `χ₃ ∉ {χ₁^{±1}, χ₂^{±1}}` and `λ₂ ≤ λ₃` are part of the
statement, not decoration**: without them the degenerate choice `χ₂ = χ₃ = χ₁`,
`ρ₂ = ρ₃ = ρ₁` satisfies every remaining hypothesis (all three minimality clauses are
instances of the global minimality of `λ₁`), and the conclusion would contradict the
certificate `Lemma10_3Cert` at every `λ₁ ≤ 6/7` — i.e. it would assert an unconditional
zero-free region with constant `6/7`, far beyond HB and false in principle.  A colleague
found this before the proof was attempted; the hypotheses above are exactly the §6
numbering that HB's §10 derivation uses (each `ρ_{j}` minimises `λ` over the pairs not
eliminated at its stage).

(The free-real-parameter form of this inequality is *false*, which is why the
setting — in particular that the `λ`'s are minimal over the zeros — is part of the
statement; the minimality is what lets the §10 argument drop the remaining zero
terms.  Note the `λ₃ ≤ 6/7` hypothesis: the §10 contradiction is *under* that
assumption.) -/
def HBLemma10_3_engine : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₃ ^ 2 = 1 → χ₁ * χ₂ * χ₃ = 1 → ρ₁.im = 0 →
      IsZ χ₂ ρ₂ → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      IsZ χ₃ ρ₃ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₁ ≤ lamOf q ρ) →
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ 1 → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        lamOf q ρ₂ ≤ lamOf q ρ) →
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ 1 → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        χ ≠ χ₂ → χ ≠ χ₂⁻¹ → lamOf q ρ₃ ≤ lamOf q ρ) →
      lamOf q ρ₂ ≤ lamOf q ρ₃ → 0 < lamOf q ρ₃ → lamOf q ρ₃ ≤ 6/7 →
      0 ≤ p1014 (lamOf q ρ₁ / (6/7)) ε

/-- **HB Lemmas 10.1, 10.2 and the `ε`-form of §10** — the remaining cases of the `λ₃` bound:
three distinct pairs with zeros of `λ < 6/7 - ε` in the rectangle contradict HB's `λ₃` bound,
whatever the numbering.  (The audit: `HBLemma10_3_engine` above is HB's *case 3* only —
`χ₁χ₂χ₃ = χ₀`, all `χ_j` real, `ρ₁` real — because that is the only case in which HB derives
(10.14) with the `P₃` budget `3φ/2`; the other cases use the `F`-method and give the `ε`-form
below.) -/
def HB10_3_Fcases : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ →
      IsZ χ₂ ρ₂ → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      IsZ χ₃ ρ₃ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      ¬ (χ₁ ^ 2 = 1 ∧ χ₂ ^ 2 = 1 ∧ χ₃ ^ 2 = 1 ∧ χ₁ * χ₂ * χ₃ = 1 ∧ ρ₁.im = 0) →
      6/7 - ε ≤ max (lamOf q ρ₂) (lamOf q ρ₃)

/-! ## HB's test functions (Conditions 1 and 2 of §§5–7) -/

/-- HB's Conditions 1 and 2 together with the Laplace transform.

* `f` is continuous on `[0,∞)`, `C²` on `(0,x₀)` with a bound `B` on `‖f''‖`
  there, supported in `[0,x₀]`, and `f ≥ 0`, `f 0 > 0` (HB §5, Condition 1
  together with the non-negativity of §6, Condition 2);
* `Fc` is the Laplace transform `z ↦ ∫₀^{x₀} e^{-zt} f t dt` (entire), and
  `Re Fc ≥ 0` on `Re z ≥ 0` — the second half of HB §6's Condition 2, which for
  HB's actual test functions holds because they are `g ∗ g` with `g ≥ 0`
  (HB §7, via (5.3), (5.4) and the maximum principle of Lemma 4.1).

All of these are needed: dropping continuity or `Re F ≥ 0` makes the inequalities
of §6 false (see the counterexample files `SpikeTestFnOutsideHBClass.lean` and
`SpikeTestFnConclusionFails.lean`, which are *not* part of this development). -/
structure TestFn where
  /-- the right end of the support (HB's `x₀`) -/
  x₀ : ℝ
  /-- HB's test function `f` -/
  f : ℝ → ℝ
  /-- the Laplace transform of `f`, for complex arguments -/
  Fc : ℂ → ℂ
  x₀_pos : 0 < x₀
  f0_pos : 0 < f 0
  f_nonneg : ∀ t : ℝ, 0 ≤ f t
  f_cont : ContinuousOn f (Set.Ici 0)
  f_diff : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀)
  f_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B
  f_supp : ∀ t : ℝ, x₀ ≤ t → f t = 0
  Fc_spec : ∀ z : ℂ, Fc z = ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)
  Fc_re_nonneg : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ (Fc z).re

/-- The Laplace transform on the real axis. -/
def TestFn.F (T : TestFn) (z : ℝ) : ℝ := (T.Fc (z : ℂ)).re

/-- HB's `F*(λ₁,λ₀) = max_{µ⁰ ∈ ℝ} Re{F(−λ₀+iµ⁰) − F(λ₁−λ₀+iµ⁰) − F(iµ⁰)}` (Lemma 6.4). -/
def TestFn.Fstar (T : TestFn) (lam₁ lam₀ : ℝ) : ℝ :=
  sSup (Set.range (fun μ : ℝ =>
    (T.Fc (((-lam₀ : ℝ) : ℂ) + (μ : ℂ) * Complex.I)
      - T.Fc (((lam₁ - lam₀ : ℝ) : ℂ) + (μ : ℂ) * Complex.I)
      - T.Fc ((μ : ℂ) * Complex.I)).re))

/-- `ψ ≤ (1/8)(k² + 1/2) + (1/6)(4k + 1)` of HB (8.11) (Lemmas 8.7 and 9.3). -/
def psi87 (k : ℝ) : ℝ := (1/8) * (k ^ 2 + 1/2) + (1/6) * (4 * k + 1)

/-- `ψ ≤ (φ/2)(k² + 4k + 3/2)` of HB Lemma 9.2, with `φ = 1/3`. -/
def psi92 (k : ℝ) : ℝ := (1/6) * (k ^ 2 + 4 * k + 3/2)

/-! ## The `F`-based engine inequalities of HB §§6–9

Each `Prop` is HB's stated inequality for a test function satisfying Conditions 1
and 2, with the hypotheses of the paper's setting.  The non-principality
hypotheses recorded are exactly those used in the corresponding positivity
identity of §6/§8/§9 (they are what makes every application of HB Lemma 5.2 legal).

Each carries the paper's setting: `IsMin1 χ₁ ρ₁` (the exceptional zero), the
real/complex case distinction, and — where `χ₁` may be real with `ρ` complex — the
exclusion of the conjugate zero (`χ₁² = 1 → ρ ≠ conj ρ₁`), which the tables' `λ₀`
and `λ_j` use.  These hypotheses were added after colleague-refutations of earlier
drafts (see `dev/README.md`).

These are the targets of the `F`-method part of AREA 3; their numerical content
(Tables 7, 9, 10, 11) is transcendental and is *not* verified here. -/

/-- **HB Lemma 6.3** (p. 29).  `ρ₁` is the exceptional zero (`IsMin1`), `χ₁` and
`ρ₁` are real, and `ρ₀ ≠ ρ₁` is a further zero of `χ₁`, maximal among the zeros of
`χ₁` other than `ρ₁`, with `λ₀ ≥ λ₁`:
`2F(−λ₀) − 2F(λ₁−λ₀) − F(0) + f(0)(1/4 + ε) ≥ 0`.

*Status.*  This is a *draft* transcription of the paper's §6 inequality: a first
draft that omitted `IsMin1` and `λ₁ ≤ λ₀` was refuted by a colleague (an in-class
test function with `λ₀ = λ₁ = 0.4`; see `dev/SpikeTestFnConclusionFails.lean.txt`).
The hypotheses `IsMin1` and `λ₁ ≤ λ₀` below are the paper's setting; whether the
maximality over the `|Im| ≤ 1` zeros is enough (the paper's rectangle (6.1) is
`|t| ≤ 𝓛`) is the point to re-check when this is proved. -/
def HBLemma6_3 : Prop :=
  ∀ (T : TestFn) (ε : ℝ), 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → lamOf q ρ₁ ≤ lamOf q ρ₀ →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
      0 ≤ 2 * T.F (-(lamOf q ρ₀)) - 2 * T.F (lamOf q ρ₁ - lamOf q ρ₀) - T.F 0
        + T.f 0 * (1/4 + ε)

/-- **HB Lemma 6.4** (p. 30), the sharpened form using `F*` in place of `−F(0)`
(same status and same caveat as `HBLemma6_3`). -/
def HBLemma6_4 : Prop :=
  ∀ (T : TestFn) (ε : ℝ), 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → lamOf q ρ₁ ≤ lamOf q ρ₀ →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
      0 ≤ T.F (-(lamOf q ρ₀)) - T.F (lamOf q ρ₁ - lamOf q ρ₀) - T.F 0
        + T.Fstar (lamOf q ρ₁) (lamOf q ρ₀) + T.f 0 * (1/4 + ε)

/-- **HB Lemma 8.5** (p. 45).  `χ₁`, `ρ₁` real with second zero `ρ₀` (maximal
`λ` among the zeros of `χ₁` other than `ρ₁`), `ρ₂` a zero of a second character
`χ₂` with `λ₂ ≤ λ₀`; the characters `χ₂, χ₁χ₂, χ₁χ̄₂` of the §6 positivity are
non-principal:
`F(−λ₂) − F(λ₁−λ₂) − F(0) + f(0)(11/24 + ε) ≥ 0`. -/
def HBLemma8_5 : Prop :=
  ∀ (T : TestFn) (ε : ℝ), 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₀ ρ₂ : ℂ),
      IsMin1 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
      IsZ χ₂ ρ₂ → χ₂ ≠ 1 → χ₁ * χ₂ ≠ 1 → χ₁ * χ₂⁻¹ ≠ 1 →
      lamOf q ρ₂ ≤ lamOf q ρ₀ →
      0 ≤ T.F (-(lamOf q ρ₂)) - T.F (lamOf q ρ₁ - lamOf q ρ₂) - T.F 0
        + T.f 0 * (11/24 + ε)

/-- **HB Lemma 8.7** (p. 46).  `χ₁`, `ρ₁` real with second zero `ρ₀`, `ρ₂` a zero
of a character `χ₂` with `χ₂⁴ ≠ χ₀` and `λ₂ ≤ λ₀`:
`(k²+1/2){F(−λ₂) − F(λ₁−λ₂)} − 2kF(0) + f(0)(ψ+ε) ≥ 0`, `ψ = psi87 k`. -/
def HBLemma8_7 : Prop :=
  ∀ (T : TestFn) (k ε : ℝ), 0 ≤ k → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₀ ρ₂ : ℂ),
      IsMin1 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → χ₂ ^ 4 ≠ 1 → IsZ χ₁ ρ₁ →
      IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
      (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
      IsZ χ₂ ρ₂ → lamOf q ρ₂ ≤ lamOf q ρ₀ →
      0 ≤ (k ^ 2 + 1/2) * (T.F (-(lamOf q ρ₂)) - T.F (lamOf q ρ₁ - lamOf q ρ₂))
        - 2 * k * T.F 0 + T.f 0 * (psi87 k + ε)

/-- **HB Lemma 9.2** (p. 55), with HB's exclusions restored (a colleague's refutation: without
them the degenerate `χ_j = χ₁`, `ρ_j = ρ₁` instance forces `λ₁ > 0.70` for every complex-character
minimiser, far beyond HB's `0.348`).  `χ₁` complex, `χ_j ∉ {χ₁^{±1}, χ₁^{±2}}`:
`(k²+1/2){F(−λ₁) − F(λ_j−λ₁)} − 2kF(0) + f(0)(ψ+ε) ≥ 0`, `ψ = psi92 k`. -/
def HBLemma9_2 : Prop :=
  ∀ (T : TestFn) (k ε : ℝ), 0 ≤ k → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ_j : DirichletCharacter ℂ q) (ρ₁ ρ_j : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → IsZ χ_j ρ_j →
      χ_j ≠ χ₁ → χ_j ≠ χ₁⁻¹ → χ_j ≠ χ₁ ^ 2 → χ_j ≠ (χ₁ ^ 2)⁻¹ →
      0 ≤ (k ^ 2 + 1/2) * (T.F (-(lamOf q ρ₁)) - T.F (lamOf q ρ_j - lamOf q ρ₁))
        - 2 * k * T.F 0 + T.f 0 * (psi92 k + ε)

/-- **HB Lemma 9.3** (p. 55), with HB's exclusions restored (same refutation as Lemma 9.2):
`χ₁` complex, `χ₂ ∉ {χ₁^{±1}}`, `χ₂² ∉ {1, χ₁^{±1}}`:
`(k²+1/2){F(−λ₁) − F(0)} − 2kF(λ₂−λ₁) + f(0)(ψ+ε) ≥ 0`, `ψ = psi87 k`. -/
def HBLemma9_3 : Prop :=
  ∀ (T : TestFn) (k ε : ℝ), 0 ≤ k → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → IsZ χ₂ ρ₂ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      0 ≤ (k ^ 2 + 1/2) * (T.F (-(lamOf q ρ₁)) - T.F 0)
        - 2 * k * T.F (lamOf q ρ₂ - lamOf q ρ₁) + T.f 0 * (psi87 k + ε)

end Work.ZeroFreeTables
