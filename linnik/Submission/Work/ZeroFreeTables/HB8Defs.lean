/-
# ZeroFreeTables — HB8Defs

The definitions and the four analytic input `Prop`s on which the proof of
**HB Lemma 8.4** (Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
least prime in an arithmetic progression*, PLMS 64 (1992) 265–338, p. 46) rests.

HB's Lemma 8.4 is proved from three alternative methods, according to the size of
`λ₁`:

* the **`F`-method / §6 triangle** (`Lemma 6.3` instantiated with the triangle test
  function `f t = max (x₀ - t) 0` of support `x₀ = 1/2 + λ₀⁻¹ + 2ε`): this gives, for
  `λ₀ ≥ 4e`, the repulsion `λ₀ ≥ (2 − ε) log(λ₁⁻¹)` — HB's **Lemma 8.1**
  (`HBLemma8_1` below).  It is available in the workspace as the proved
  `Submission.Work.LinnikAreas.DhRepel.lemma6_3_fullH` (the free-box-height form of
  HB's `Lemma 6.3`);

* the **`F`-method with the optimal test function of §7** (`Lemma 7.1`/`7.5` at
  `k = 2/3`), i.e. **Tables 2 and 3** of HB (p. 38): these give the repulsion in the
  complementary range `λ₀ < 4e` and the ε-free bound `λ₀ ≥ (3/2) log(λ₁⁻¹)`.
  Stated as `HBTable2and3` below;

* the **`P₃` method of §8.3/§9** (`Lemma 8.3` + the `µ⁰ = 0` case of Lemma 6.4, i.e.
  **Table 4** of HB (p. 43), available in the workspace as
  `Work.ZeroFreeTables.Table4Defs.HBLemma8_2`/`HBLemma8_3` plus their certificate):
  this gives the ε-free bounds of Table 4 for `λ₁ ≥ 0.4` (`HBTable4range` below).

The repeated-zero case (`ρ₁` a multiple zero) is HB's "or a repeated zero `ρ₀ = ρ₁`"
of §6; in the repeated case the bound of Table 4 is `λ₁ ≥ 1.724` (HB Table 4's entry
at `λ₁ ≤ 0.7`), and `λ₁ ≥ 1.294` is what Lemma 8.4 needs (`HBRepZero84` below).

Everything is stated in the vocabulary of the frozen contract (`Work.LinnikContract`,
`Work.ZeroFreeTables.API`) with HB's §6 numbering `IsMin1WideAt 10`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The §6 triangle method: HB Lemma 8.1 -/

/-- **HB Lemma 8.1** (p. 37), in the form needed by Lemma 8.4.

`χ₁` is a real character (`χ₁² = 1`) with a real exceptional zero `ρ₁`
(`IsMin1WideAt 10`), `λ₁ = λ(ρ₁) ≤ 0.2`, and `ρ₀ ≠ ρ₁` is the zero of `χ₁` of
*minimal* `λ` among the zeros of the working region.  Then, whenever `λ₀ ≥ 4e`,

  `λ₀ ≥ (2 − ε) log(λ₁⁻¹)`   for `q ≥ q₀(ε)`.

This is HB's `Lemma 8.1` ("under the conditions of Lemma 6.3, either `λ₀ < 4e` or
`λ₀ ≥ (2−ε)log(λ₁⁻¹)`"): the derivation applies `Lemma 6.3` (proved in the workspace
as `Work.LinnikAreas.DhRepel.lemma6_3_fullH`, with the free box height
`Hh = |γ₀| + 1/2 ≤ 3/2 ≤ 10` supplied by `IsMin1WideAt 10`) to the triangle test
function `f t = max (x₀ − t) 0` with `x₀ = 1/2 + λ₀⁻¹ + 2ε`, uses
`2F(−λ₀) − 2F(λ₁−λ₀) ≤ 2x₀λ₁λ₀⁻²e^{x₀λ₀}` and `F(0) = x₀²/2` to get
`λ₁ ≥ (λ₀/(4e))e^{-x₀λ₀}` for `λ₀ ≥ 4e`, and inverts.  The ε is renamed at the
end (`ε ↦ ε/8`). -/
def HBLemma8_1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
      (∀ u : ℂ, IsZ χ₁ u → u ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q u) →
      lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ lamOf q ρ₀ →
      (2 - ε) * Real.log (1 / lamOf q ρ₁) ≤ lamOf q ρ₀

/-! ## The §7 optimal test function: HB Tables 2 and 3 -/

/-- **HB Tables 2 and 3** (p. 38), the `F`-method of §8 with the optimal test
function of `Lemma 7.1`/`7.5` at `k = 2/3`.

For a real character `χ₁` with real exceptional zero `ρ₁` and `λ₁ = λ(ρ₁)`:

* if `λ₁ ≤ 0.2` then every *other* zero `ρ` of `χ₁` in the working region satisfies
  `λ(ρ) ≥ min(4e, (2−ε)log(λ₁⁻¹))`   (Table 2: the entries `λ₁ ↦ λ₀` are
  `0.006 ↦ 11.34`, …, `0.20 ↦ 3.35`, all exceeding `2 log(λ₁⁻¹)`, and `11.34 > 4e`);
* if `λ₁ ≤ 0.4` then `λ(ρ) ≥ max((3/2) log(λ₁⁻¹), 1.294)`   (Tables 2 and 3: the
  entries at `λ₁ = 0.2, 0.25, 0.3, 0.35, 0.4` are `3.35, 2.84, 2.43, 2.09, 1.80`,
  all exceeding `(3/2)log(λ₁⁻¹) = 2.41, 2.08, 1.81, 1.57, 1.37`).

Route: HB's `Lemma 6.3` with the `Lemma 7.1` test function (the workspace's
`Work.ZeroFreeTables.testFn7_1`); the inequality
`F(−λ₀) − F(λ₁−λ₀) = ∫₀^∞ f(t)e^{λ₀t}(1−e^{−λ₁t})dt` is increasing in both `λ₁`
and `λ₀`, and the tabulated `λ₀b` is defined by
`2F(−λ₀b) − 2F(b−λ₀b) − F(0) + f(0)/4 = 0`, so that `λ₀ ≥ λ₀b − ε` for
`q ≥ q(ε,b)` whenever `0 ≤ λ₁ ≤ b`; `Lemma 7.5` gives `F(−λ) − kF(0) = −λ⁻¹f(0)cos²θ`
with `sin²θ = k(1−θ cot θ)`, `k = 2/3`.  The numerical content is the interval
arithmetic on `F` at the tabulated rationals. -/
def HBTable2and3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamS ≤ lamOf q ρ₁ →
      (lamOf q ρ₁ ≤ 1 / 5 →
        Lam0BoundOther χ₁ ρ₁ (min (4 * Real.exp 1) ((2 - ε) * Real.log (1 / lamOf q ρ₁)))) ∧
      (lamOf q ρ₁ ≤ 2 / 5 →
        Lam0BoundOther χ₁ ρ₁ (max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000)))

/-! ## The §8.3 `P₃` method: the range of HB Table 4 -/

/-- **HB Table 4** (p. 43), middle/large range, in the form Lemma 8.4 needs.

This is the content of HB's Table 4 for `0.4 ≤ λ₁ ≤ 1.294` — where the `P₃` method
of `Lemma 8.3` (and, when `ρ₀` is real, the `µ⁰ = 0` case of `Lemma 6.4`, i.e.
`Lemma 8.2`) beats the `F`-method.  It is derived from
`Work.ZeroFreeTables.Table4Defs.HBLemma8_2` and `HBLemma8_3` together with the
per-row certificate (the `a`, `K` witnesses and the (8.6)/(8.7) arithmetic), exactly
as `HBTable8_of_engine` derives Table 8 from `HBLemma9_1` and its certificate.

Only the closing part of Table 4 is needed here: for `λ₁ ≤ 1.294` the entry at
`λ₁ = 1.294` gives `λ₀ ≥ 1.294`, and the entries at `λ₁ = 0.4, …, 1.275` give the
slightly larger values needed for `(3/2)log(λ₁⁻¹) > 1.294`, i.e. `λ₁ < 0.422`. -/
def HBTable4range : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      2 / 5 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ 1294 / 1000 →
      Lam0BoundOther χ₁ ρ₁ (max ((3 / 2) * Real.log (1 / lamOf q ρ₁)) (1294 / 1000))

/-! ## The repeated-zero case of §6 -/

/-- **HB §6, repeated-zero case.**  If the exceptional real zero `ρ₁` of a real
character `χ₁` is a *multiple* zero (`2 ≤ zeroMult χ₁ ρ₁`), then `λ₁ ≥ 1.294`.

HB's §6 considers "a repeated zero `ρ₀ = ρ₁`" of `L(s, χ₁)`; there `λ₀ = λ₁`, and the
`µ⁰ = 0` case of Lemma 6.4 with the optimal test function at `k = 2` gives
`λ₁ ≥ 2.427…` (HB's Lemma 8.2), of which `1.294` is what Lemma 8.4 needs.  The
same bound is Table 4's entry at `λ₁ = 1.294` read in the repeated case. -/
def HBRepZero84 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      2 ≤ zeroMult χ₁ ρ₁ → 1294 / 1000 ≤ lamOf q ρ₁

/-! ## HB's `φ = 1/4` input for real characters (available in the workspace)

HB's §8 constants are stated with `φ(χ₁) = 1/4`, which his Lemma 2.5 supplies for
characters of order at most `L` — in particular for every **real** `χ₁` (order `2`).
The workspace's `φ = 1/3` provider (`Work.LinnikAreas.l52HypRealFixed`) is *not* sharp
enough for Lemma 8.4's first conjunct: for the triangle method of §8.1 with support
`x₀ = λ₀⁻¹ + 2(2c + 4ε)` (`c = φ/2`) one gets the repulsion constant `1/(2φ)`, i.e. `2`
for `φ = 1/4` but only `3/2` for `φ = 1/3`.

The sharp input **is** available, as

* `Work.ZeroFreeTables.Table4.l52HypRealQuarter` (proved, sorry-free):
  `∃ c, 0 < c ∧ c ≤ 1/8 + 10⁻⁶ ∧ ∃ δ ∈ (0,1), ∃ q₀, ∀ q ≥ q₀, ∀ real non-principal χ,
  ∀ ε ∈ (0,1], L52Hyp χ c ε δ`,

obtained from Burgess' `k = 4` bound via `quarterBoundReal`.  NB the exact constant `1/8`
is *not* attainable together with a single `δ` serving all `ε`: HB's Lemma 3.1 produces
`δ = δ(ε)`, and the admissible radius shrinks with the slack (a delegated prover settled
this), so `c ≤ 1/8 + 10⁻⁶` with an `ε`-independent `δ` is the sharp form.  An earlier
`Prop` of the present file asserting `c = 1/8` exactly was therefore *false* and has been
removed. -/

end Work.ZeroFreeTables
