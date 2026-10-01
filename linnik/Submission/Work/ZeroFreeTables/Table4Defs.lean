/-
# ZeroFreeTables — Table4Defs

The definitions and the two analytic input `Prop`s on which the proof of
**HB Table 4** (Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
least prime in an arithmetic progression*, PLMS 64 (1992) 265–338, p. 43) rests.

Table 4 is the table of the bound `λ₀ ≥ v` for real `χ₁` and real `ρ₁`, and is
derived in the paper from two of the §8 inequalities:

* **HB Lemma 8.3** (p. 42, the `P₃` method).  For positive `a`, `K` and the side
  condition (8.6) `(a+λ₀)⁻³ + (a+λ₁)⁻³ ≥ a⁻³`,

    `(K² + 1/2)(P₃((a+λ₁)/a) − P₃(1)) − 2K P₃((a+λ₁)/(a+λ₀)) + (K+1)²(a+λ₁)(1/8 + ε) ≥ 0`  (8.7)

  where `P₃(X) = X + X² + (2/3)X³` is HB (4.12)'s third polynomial, `λ₁ = λ(ρ₁)` and
  `λ₀ = λ(ρ₀)` for the two zeros `ρ₁, ρ₀` of `χ₁`.  This is the method that produces
  Table 4's middle/large range (`λ₁ ≥ 0.3`), where it beats the `F`-method (see HB's
  remark after Table 4: "Lemma 8.3 is sharper than Lemma 8.1 for values of `λ₁` from
  around 0.35 onwards").  It is stated here for the case in which the second zero
  `ρ₀` is **not real** (`ρ₀.im ≠ 0`): the derivation runs at the three points
  `σ, σ+iγ⁰, σ+2iγ⁰` (`γ⁰ = Im ρ₀`), which collapse when `ρ₀` is real.

* **HB Lemma 8.2** (p. 42, the `F` method, `µ⁰ = 0` case).  For real `χ₁, ρ₁, ρ₀`
  (the second zero `ρ₀` maximal, i.e. of minimal `λ`) one has `λ₀ ≥ 2.427…`.  Stated
  here with the rational constant `2.293` (the largest value needed by Table 4),
  together with the repeated-zero case `ρ₀ = ρ₁` (multiplicity `≥ 2`), in which the
  same derivation applies with `λ₁` in place of `λ₀`: HB's "Suppose that `L(s,χ₁)`
  has a zero `ρ₀ ≠ ρ₁` in `R` (or a repeated zero `ρ₀ = ρ₁`)".

Both are stated in the vocabulary of the frozen contract (`Work.LinnikContract`) and
of `Work.ZeroFreeTables.Engine`, and with HB's §6 numbering
(`IsMin1WideAt 10`, i.e. `λ₁` minimal among the zeros of all non-principal
characters in the strip `|Im| ≤ 10`).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The `P₃` inequality of HB Lemma 8.3 (§8.2, second method) -/

/-- **HB (8.6)**, the side condition of Lemma 8.3: `(a+λ₀)⁻³ + (a+λ₁)⁻³ ≥ a⁻³`. -/
def cond86 (lam₁ lam₀ a : ℝ) : Prop :=
  1 / (a + lam₀) ^ 3 + 1 / (a + lam₁) ^ 3 ≥ 1 / a ^ 3

/-- **HB (8.8)**, the sufficient condition for (8.7) to be non-decreasing in `λ₁`:

`((K² + 1/2)/a)(1 + 2(a+λ₁)/a + 2((a+λ₁)/a)²) + (K+1)²/8 ≥ 10K/(a+λ₁)`.

(HB's derivation: the derivative of (8.7) in `λ₁` is at least the left hand side
minus `2K P₃'(1)/(a+λ₀) ≥ 10K/(a+λ₁)`, since `λ₀ ≥ λ₁`.) -/
def cond88 (lam₁ a K : ℝ) : Prop :=
  ((K ^ 2 + 1/2) / a) * (1 + 2 * (a + lam₁) / a + 2 * ((a + lam₁) / a) ^ 2)
      + (K + 1) ^ 2 / 8 ≥ 10 * K / (a + lam₁)

/-- The left hand side of HB (8.7), without the `ε`-term. -/
def p83 (lam₁ lam₀ a K : ℝ) : ℝ :=
  (K ^ 2 + 1/2) * (P3R ((a + lam₁) / a) - P3R 1)
    - 2 * K * P3R ((a + lam₁) / (a + lam₀)) + (K + 1) ^ 2 * (a + lam₁) * (1/8)

/-- **HB Lemma 8.3** (p. 42), engine form, for a **non-real** second zero `ρ₀`.

For every `a > 0`, `K ≥ 1/4` and `ε > 0` there is `q₀` such that for `q ≥ q₀`, if
`χ₁` is a real non-principal character mod `q`, `ρ₁` is its exceptional zero
(`IsMin1WideAt 10`, `ρ₁` real), and `ρ₀ ≠ ρ₁` is a further zero of `χ₁` in the
working region with `ρ₀.im ≠ 0` and `λ(ρ₁) ≤ λ(ρ₀)`, then, whenever the side
condition (8.6) holds at `(λ(ρ₁), λ(ρ₀))`,

`0 ≤ (K² + 1/2)(P₃((a+λ₁)/a) − P₃(1)) − 2K P₃((a+λ₁)/(a+λ₀)) + (K+1)²(a+λ₁)(1/8 + ε)`.

Route (HB §8.2): the pointwise inequality `(1 + χ₁(n))(K + Re(χ₁(n)n^{-iγ⁰}))² ≥ 0`
(expansion: `(K² + 1/2)(χ₀(n) + χ₁(n)) + 2K Re((χ₀(n)+χ₁(n))n^{-iγ⁰})
+ (1/2)Re((χ₀(n)+χ₁(n))n^{-2iγ⁰})`, cf. HB (8.5) and the workspace's
`P3.Pointwise91`/`Ksum_positivity`), the near/far split of the `P₃`-weighted
explicit formula of `L'/L` (`P3.CompletedDerivPF`, `P9.lDiffExplicit_gen`), HB
Lemma 3.1 for the `k = 1` term, HB Lemma 5.3 for the principal character, the
positivity `Re P₃((σ-1)/(s-ρ)) ≥ 0` of (4.11) to drop the remaining near zeros
(`P3Pos`), the bound `Re P₃(α/(β+it)) ≥ (8/3)αβ³/(β²+t²)³` for `β ≥ α` (giving the
`ρ₀`-term at `µ⁰ = 0`), and finally `A, B ≥ 0` from (8.6) via the `Re P₃`
comparisons (`P3.P3Bounds`, `P3.CaseC_D`). -/
def HBLemma8_3 : Prop :=
  ∀ (a K ε : ℝ), 0 < a → 1/4 ≤ K → 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → lamOf q ρ₁ ≤ lamOf q ρ₀ →
      cond86 (lamOf q ρ₁) (lamOf q ρ₀) a →
      0 ≤ p83 (lamOf q ρ₁) (lamOf q ρ₀) a K + (K + 1) ^ 2 * (a + lamOf q ρ₁) * ε

/-! ## The `µ⁰ = 0` case of the `F`-method: HB Lemma 8.2 and the repeated zero -/

/-- **HB Lemma 8.2** (p. 42) and the repeated-zero case, in the form needed by
Table 4.

`χ₁` is real (`χ₁² = 1`, hence of order `2`) and `ρ₁` is its exceptional zero
(`IsMin1WideAt 10`), real.  Then:

* if `ρ₁` is a **repeated** zero (`2 ≤ zeroMult χ₁ ρ₁`), then `λ(ρ₁) ≥ 2.293`;
* if `ρ₀ ≠ ρ₁` is a **real** further zero of `χ₁` of minimal `λ` among the zeros of
  the working region, then `λ(ρ₀) ≥ 2.293`.

This is HB's `µ⁰ = 0` case of §6 (his `ρ₀` real, "(6.18)" with `µ⁰ = 0`), where the
two points `β⁰` and `β⁰ + iγ⁰` of the derivation coincide, so that the two `χ₁`-sums
each contribute the `ρ = ρ₀` term: `2F(−λ₀) − 2F(λ₁−λ₀) − 2F(0) + f(0)(1/4 + ε) ≥ 0`
(the sharpened form of Lemma 6.3, whose `2F(0)` is what makes the argument work).
With the optimal test function of HB §7 corresponding to `k = 2` (`sin²θ = 2(1−θcotθ)`,
`θ = 0.9873…`) this gives `λ₀⁻¹cos²θ ≤ 1/8 + ε`, i.e. `λ₀ ≥ 2.427…`; any
`θ ∈ (0.86, 1.14)` (e.g. `θ = 1`) gives the stated rational constant `2.293`.

The maximality hypothesis `∀ ρ, IsZ χ₁ ρ → ρ ≠ ρ₁ → λ(ρ₀) ≤ λ(ρ)` is the paper's
"Choose such a zero `ρ₀` with `Re(ρ₀)` maximal", which is what lets the contributions
of the remaining near zeros be dropped (`Re F ≥ 0`, HB's Condition 2). -/
def HBLemma8_2 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ →
      (2 ≤ zeroMult χ₁ ρ₁ → 2293/1000 ≤ lamOf q ρ₁) ∧
      ∀ ρ₀ : ℂ, IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ → ρ₀.im = 0 →
        (∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → lamOf q ρ₀ ≤ lamOf q ρ) →
        2293/1000 ≤ lamOf q ρ₀

end Work.ZeroFreeTables
