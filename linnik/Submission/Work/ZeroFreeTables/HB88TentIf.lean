/-
# ZeroFreeTables — HB88TentIf

Interfaces for the tent-function route to `Work.ZeroFreeTables.HBLemma8_8`.

The two *engine* bodies below are the tent instantiations of
`Work.ZeroFreeTables.lemma85pt_region_mixed` (HB Lemma 8.5, five-term, mixed constants
`1/8 + 2·(1/6) = 11/24`) and of
`Work.LinnikAreas.DhRepel.lemma6_3_fullH` (HB Lemma 6.3, same-character, constant `2c = 1/4`
for a real `χ`), with the test function specialised to the tent `tent X` of
`HB88TentDefs`:

* `TentFiveBodyAt X A ε δ q` — the five-term configuration at level `q` implies
  `0 ≤ tentFive X A λ₁ λ₂`.
* `TentSameBodyAt X A ε δ q` — the same-character configuration at level `q` implies
  `0 ≤ tentSame X A λ₁ λ'`.

Both are stated with the four (resp. one) `L52Hyp` supplies as *hypotheses*, so that the
`L52Hyp` supply machinery is shared by all instantiations.

The extraction lemmas (`tentFm_sub_le`, `tentFive_crude`, `tentSame_crude`, `tentFive_mono`)
are pure real analysis on `tentFm` and carry no number theory.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88TentDefs
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- **The five-term configuration of HB Lemma 8.5 at the tent of width `X`.**  Given the four
`L52Hyp` supplies (with the mixed constants `c₁ = 1/8` for `χ₁` and `c = 1/6` for the other
three characters) and the five-term configuration of HB §6/§8 — the pair `(χ₁,β₁)` real,
`(χ₂, β₂ + iγ₂)` with the ball maximalities `hmaxA…hmaxD`, the `χ₁`-window `hmaxC`, the two
divisor conditions and the point/height conditions — the tent's five-term combination

`tentFive X A λ₁ λ₂ = ∫ tent e^{λ₂t} - ∫ tent e^{(λ₂-λ₁)t} - ∫ tent + X·A`

is nonnegative, with `λ₁ = log q·(1-β₁)`, `λ₂ = log q·(1-β₂)` and `A = 11/24 + 4ε`. -/
def TentFiveBodyAt (X A ε δ : ℝ) (q : ℕ) : Prop :=
  ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    [NeZero χ₁.conductor] [NeZero χ₂.conductor]
    [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₁ * χ₂⁻¹).conductor]
    {β₁ β₂ γ₂ : ℝ},
    χ₁ ≠ 1 → χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₁ * χ₂ ≠ 1 → χ₁ * χ₂⁻¹ ≠ 1 →
    |1 - β₁| ≤ δ → |1 - β₂| ≤ δ → |γ₂| + 1 ≤ 10 * Real.log (q : ℝ) →
    |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    |1 - β₂| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    DirichletCharacter.LFunction χ₂ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) = 0 →
    (∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
      |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂) →
    (∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂⁻¹).primitiveCharacter u = 0 →
      |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂) →
    (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = (β₁ : ℂ) ∨ u.re ≤ β₂) →
    (∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
      |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂) →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|γ₂| + 2))) (β₁ : ℂ) ≠ 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|γ₂| + 2))) ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) ≠ 0 →
    Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) ε δ →
    Commons.NumberTheory.Linnik.L52Hyp χ₂ (1/6) ε δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) (1/6) ε δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) (1/6) ε δ →
    0 ≤ tentFive X A (Real.log (q : ℝ) * (1 - β₁)) (Real.log (q : ℝ) * (1 - β₂))

/-- **The same-character configuration of HB Lemma 6.3 at the tent of width `X`.**  Given the
`L52Hyp` supply for the real character `χ` with constant `c = 1/8`, the two points
`β₁` and `β' + iγ'` (with `β₁` simple at the divisor level, and the maximality `hmax`: the only
zero of `χ` with `|Im| ≤ Hh` and `re > β'` is `β₁`), the rectangle (`hrect`) and point
conditions, the tent's same-character combination
`tentSame X A λ₁ λ' = 2∫ tent e^{λ't} - 2∫ tent e^{(λ'-λ₁)t} - ∫ tent + X·A`
is nonnegative, with `A = 1/4 + 4ε`. -/
def TentSameBodyAt (X A ε δ : ℝ) (q : ℕ) : Prop :=
  ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {β₁ β' γ' Hh : ℝ},
    χ ≠ 1 → χ * χ = 1 →
    |1 - β₁| ≤ δ → |1 - β'| ≤ δ → β₁ ≤ 1 → β' ≤ 1 →
    |γ'| + δ ≤ Hh → |γ'| ≤ 10 * Real.log (q : ℝ) →
    |1 - β₁| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    |1 - β'| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) ≠ 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 →
    ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ (β₁ : ℂ) →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) = 1 →
    (∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
      |u.im| ≤ Hh → u = (β₁ : ℂ) ∨ u.re ≤ β') →
    Real.log (q : ℝ) * (1 - β₁) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    Real.log (q : ℝ) * (1 - β') ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
    Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ →
    0 ≤ tentSame X A (Real.log (q : ℝ) * (1 - β₁)) (Real.log (q : ℝ) * (1 - β'))

/-! ## The tent row table

The finite table of rows `(X, b, c)` covering the region `λ₁ ≤ 0.0797`, `λ₂ ≤ 15437/1000`: for
each row the *sharp* certificate

`b·e^{Xc}·((Xc - 2) + (Xc + 2)e^{-Xc}) < X·(X/2 - A₀)·c³`

holds (with `A₀ = 11/24 + 4/10⁴` the worst-case slack `4ε` over `ε ≤ 1/100`), and the chain
condition `c_i ≥ (12/11)·log(1/b_{i+1})` holds, so that the rows cover the whole staircase
`λ₂ < (12/11)·log(1/λ₁)`.  The rows come in five widths `X ∈ {1, 6/5, 21/20, 11/10, 23/20}`. -/

/-- The worst-case five-term slack `A₀ = 11/24 + 4ε` at `ε = 1/100`. -/
def A₀ : ℝ := 11 / 24 + 4 / 10000

/-- The worst-case same-character slack `A₀' = 1/4 + 4ε` at `ε = 1/100`. -/
def As₀ : ℝ := 1 / 4 + 4 / 10000

/-- The rows `(X, b, c)` of the tent table. -/
def tentRows : List (ℝ × ℝ × ℝ) :=
  [ ((6/5 : ℝ), (79700000 : ℝ)/10^9, (2840 : ℝ)/1000),
    ((6/5 : ℝ), (74094301 : ℝ)/10^9, (2932 : ℝ)/1000),
    ((6/5 : ℝ), (68101912 : ℝ)/10^9, (3038 : ℝ)/1000),
    ((6/5 : ℝ), (61795999 : ℝ)/10^9, (3157 : ℝ)/1000),
    ((23/20 : ℝ), (55409734 : ℝ)/10^9, (3292 : ℝ)/1000),
    ((23/20 : ℝ), (48960081 : ℝ)/10^9, (3447 : ℝ)/1000),
    ((23/20 : ℝ), (42475267 : ℝ)/10^9, (3624 : ℝ)/1000),
    ((23/20 : ℝ), (36113688 : ℝ)/10^9, (3824 : ℝ)/1000),
    ((23/20 : ℝ), (30064306 : ℝ)/10^9, (4047 : ℝ)/1000),
    ((11/10 : ℝ), (24506098 : ℝ)/10^9, (4294 : ℝ)/1000),
    ((11/10 : ℝ), (19540814 : ℝ)/10^9, (4577 : ℝ)/1000),
    ((11/10 : ℝ), (15075767 : ℝ)/10^9, (4897 : ℝ)/1000),
    ((11/10 : ℝ), (11243108 : ℝ)/10^9, (5253 : ℝ)/1000),
    ((11/10 : ℝ), (8112629 : ℝ)/10^9, (5644 : ℝ)/1000),
    ((21/20 : ℝ), (5668958 : ℝ)/10^9, (6075 : ℝ)/1000),
    ((21/20 : ℝ), (3818746 : ℝ)/10^9, (6559 : ℝ)/1000),
    ((21/20 : ℝ), (2450410 : ℝ)/10^9, (7095 : ℝ)/1000),
    ((21/20 : ℝ), (1499186 : ℝ)/10^9, (7680 : ℝ)/1000),
    ((21/20 : ℝ), (876931 : ℝ)/10^9, (8310 : ℝ)/1000),
    ((21/20 : ℝ), (492221 : ℝ)/10^9, (8980 : ℝ)/1000),
    ((1 : ℝ), (266337 : ℝ)/10^9, (9714 : ℝ)/1000),
    ((1 : ℝ), (135902 : ℝ)/10^9, (10514 : ℝ)/1000),
    ((1 : ℝ), (65275 : ℝ)/10^9, (11377 : ℝ)/1000),
    ((1 : ℝ), (29593 : ℝ)/10^9, (12297 : ℝ)/1000),
    ((1 : ℝ), (12733 : ℝ)/10^9, (13269 : ℝ)/1000),
    ((1 : ℝ), (5224 : ℝ)/10^9, (14287 : ℝ)/1000),
    ((1 : ℝ), (2055 : ℝ)/10^9, (15344 : ℝ)/1000)]

/-- The sharp row certificate for the row `(X,b,c)`: a strict inequality, free of cancellation,
which by `tentFive_sharp` implies `tentFive X A₀ b c < 0`. -/
def TentRowCert (p : ℝ × ℝ × ℝ) : Prop :=
  p.2.1 * Real.exp (p.1 * p.2.2) * ((p.1 * p.2.2 - 2) + (p.1 * p.2.2 + 2) * Real.exp (-(p.1 * p.2.2)))
    < p.1 * (p.1 / 2 - A₀) * p.2.2 ^ 3

end Work.ZeroFreeTables
