import ChallengeDeps
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto

/-!
# `Work.RHPlan.Defs` — definitions and area statements for the Lagarias-criterion project

This module fixes the vocabulary in which the contract
`Work.RHPlan.rh_iff_of_areas` (file `Submission/Work/RHPlan/Interfaces.lean`) is expressed.

## The two inequality predicates

* `RobinBound n` is Robin's inequality `σ(n) ≤ e^γ n log log n` at the integer `n`.
* `LagariasBound n` is Lagarias' elementary inequality
  `σ(n) ≤ H_n + exp(H_n) log(H_n)` at `n`; the challenge's `LagariasElementaryCriterion`
  is `∀ n, 0 < n → LagariasBound n` (definitionally).

## The colossally abundant (CA) parametrisation

The whole arithmetic content of Robin's Theorem 1 is concentrated on *colossally abundant*
numbers, i.e. the values of the product
`N_ε = ∏_{p < ⌈e^{2/ε}⌉+2, p prime} p ^ ⌊ log((p^{1+ε}-1)/(p^{1+ε}-p)) / log p ⌋₊`
(Nicolas (4.11), the parametrisation used throughout `Commons.NumberTheory.Robin`).
`caNumber ε` is *literally* the product appearing in the hypothesis of
`Commons.NumberTheory.Robin.robin_of_ca_cover`, so the two unfold to the same term.

`caXi ε` is the largest prime in the support
`caSupport ε = {p prime : p < ⌈e^{2/ε}⌉+2, 1 ≤ ⌊μ(p,ε)⌋₊}`,
i.e. the largest prime factor of `N_ε`.  (`caXi` is `⊤`-valued at `0` for `ε ≤ 0`; every use
below carries `0 < ε`.)

## The four areas

* `RobinLargeXiCAInput`  — Robin's inequality at CA numbers with large `ξ` (the analytic part
  of Robin's Theorem 1, carried out in practice by Nicolas' Prop 5.1 margin argument from an
  *effective* sharp Mertens-3 estimate).
* `RobinSmallXiCAInput`  — Robin's inequality at CA numbers with small `ξ` (a certified finite
  table over finitely many explicit integers).
* `MertensErrorOscillationOfZeroOffLine` — an off-line zero of `ζ` forces the Mertens-3 error
  `logRatioSum x − γ − log log x` to be positive of size `x^{b-1}/log x` infinitely often
  (Landau/Nicolas' oscillation).
* `RobinOscillationOfMertensError` — that oscillation transfers to Robin's counterexamples
  (`σ(n)/n` exceeding `e^γ log log n` by a relative amount `C/(log n)^β`), by evaluating at
  `n = lcm(1,…,⌊x⌋)`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHPlan

noncomputable section

/-! ## Basic inequality predicates -/

/-- Robin's inequality `σ(n) ≤ e^γ · n · log log n`. -/
def RobinBound (n : ℕ) : Prop :=
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- Lagarias' elementary inequality `σ(n) ≤ H(n) + exp(H(n)) · log(H(n))`. -/
def LagariasBound (n : ℕ) : Prop :=
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
    (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- The challenge's `LagariasElementaryCriterion`, restated through `LagariasBound`.
This is a definitional unfolding; it is recorded so that the contract can speak about
`LagariasBound` instead of the raw formula. -/
theorem lagariasElementaryCriterion_iff :
    LeanEval.NumberTheory.LagariasElementaryCriterion ↔ ∀ n : ℕ, 0 < n → LagariasBound n :=
  Iff.rfl

/-! ## The colossally abundant parametrisation -/

/-- The exponent `μ(p,ε) = log((p^{1+ε}-1)/(p^{1+ε}-p)) / log p` of the prime `p` in `N_ε`. -/
def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The colossally abundant number
`N_ε = ∏_{p < ⌈e^{2/ε}⌉+2, p prime} p ^ ⌊μ(p,ε)⌋₊` of Nicolas (4.11); it is the product
appearing verbatim in the statement of `Commons.NumberTheory.Robin.robin_of_ca_cover`. -/
def caNumber (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
    (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)

/-- The prime support of `N_ε`: the primes `p < ⌈e^{2/ε}⌉+2` with `1 ≤ ⌊μ(p,ε)⌋₊`. -/
def caSupport (ε : ℝ) : Finset ℕ :=
  ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
    (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)

/-- `ξ(ε)`: the largest prime in the support of `N_ε`, i.e. the largest prime factor of `N_ε`
(as a natural number; it is `0` when the support is empty). -/
def caXi (ε : ℝ) : ℕ := (caSupport ε).sup id

/-- `M` is a value of the colossally abundant family: `M = N_ε` for some `ε > 0`. -/
def IsColossallyAbundant (M : ℕ) : Prop := ∃ ε : ℝ, 0 < ε ∧ caNumber ε = M

/-- The explicit threshold used to split the CA range in the contract: `ξ₀ = 10^4`.
Below it Robin's inequality at CA numbers is a certified finite computation; above it the
analytic (Nicolas/Prop 5.1) argument applies. -/
def xiSplitThreshold : ℝ := 10000

/-! ## The four areas -/

/-- **AREA 1 (`RobinLargeXiCAInput`).**

Robin's inequality at every colossally abundant number `N_ε ≥ 55441` whose largest prime
factor satisfies `ξ(ε) ≥ 10^4` — the *analytic* half of Robin's Theorem 1 (Robin 1984),
in the form in which Nicolas' argument delivers it: the CA margin inequality
`C/(√ξ log ξ) ≤ logloglog N_ε − loglog θ(ξ) − caCorrSum ε`
together with the sharp Mertens-3 estimate `logRatioSum ξ ≤ γ + log log θ(ξ) + C/(√ξ log ξ)`
sum to Robin's bound (`Commons.NumberTheory.Robin.robin_Neps_of_margin`).

**Status.** Both ingredients are proved in the commons
(`Commons.NumberTheory.Zeta.log_f_lower_sharp_explicit`,
`Commons.NumberTheory.Robin.hmargin_large`), but only with *ineffective/astronomical*
thresholds (`ξ₀ ≥ 10^100` for the margin, `x₀ = exp(exp(10^7+))` for the sharp ψ bound).
`RobinLargeXiCAInput` records the statement with a *usable* threshold `10^4`; its proof
requires an effective sharp explicit formula for `ψ` (Schoenfeld's
`|ψ(x) − x| ≤ √x (log x)²/(8π)` for `x ≥ 73.2` is the classical input) and a re-run of the
Nicolas margin chain with the resulting constants.  This is a true statement: under RH,
Robin's inequality holds for every `n ≥ 5041`. -/
def RobinLargeXiCAInput : Prop :=
  RiemannHypothesis → ∀ ε : ℝ, 0 < ε → 55441 ≤ caNumber ε →
    xiSplitThreshold ≤ (caXi ε : ℝ) → RobinBound (caNumber ε)

/-- **AREA 2 (`RobinSmallXiCAInput`).**

Robin's inequality at every colossally abundant number `N_ε ≥ 55440` whose largest prime
factor satisfies `ξ(ε) < 10^4`.  There are only finitely many such integers (each is
`∏_{p < 10^4} p^{a_p}` for an exponent vector produced by the CA rule, of size `e^{10^4}` at
most), so this is a *certified finite computation*: the statement is unconditional and can be
discharged by a table in the style of `Commons.NumberTheory.Robin.finiteRange_*`, which
already verifies Robin's inequality for every `n ∈ [5041, 55440]`.

**Status.** Not yet proved.  It is true (under RH by Robin's theorem; and the CA numbers with
`ξ < 10^4` are far from the failing range `ξ^{1/2-b} ≳ log ξ` that Robin's Theorem 2 produces
when RH fails), and it is *decidable by computation* — that is the content of the area. -/
def RobinSmallXiCAInput : Prop :=
  ∀ ε : ℝ, 0 < ε → 55440 ≤ caNumber ε → (caXi ε : ℝ) < xiSplitThreshold → RobinBound (caNumber ε)

/-! ## The Mertens-3 error and its oscillation -/

/-- The `logRatioSum` of `Commons.NumberTheory.Mertens`, i.e. `Σ_{p ≤ x} log(p/(p-1))`
(Mertens' third-theorem sum). -/
abbrev logRatioSum (x : ℝ) : ℝ := Commons.NumberTheory.Mertens.logRatioSum x

/-- The Mertens-3 error `E(x) = Σ_{p ≤ x} log(p/(p-1)) − γ − log log x`. -/
def mertensError (x : ℝ) : ℝ :=
  logRatioSum x - Real.eulerMascheroniConstant - Real.log (Real.log x)

/-- `E(x) = mertensError x` is positive of size `c · x^{b-1}/log x` for arbitrarily large `x`. -/
def MertensErrorOscillation (b c : ℝ) : Prop :=
  0 < c ∧ ∀ x₀ : ℝ, ∃ x : ℝ, x₀ ≤ x ∧
    c * x ^ (b - 1) / Real.log x ≤ mertensError x

/-- **AREA 3 (`MertensErrorOscillationOfZeroOffLine`).**

A zero `ρ` of `ζ` with real part `b = Re ρ ∈ (1/2, 1)` forces the Mertens-3 error to be
*positive* of size `x^{b-1}/log x` for arbitrarily large `x`.  This is the Landau/Nicolas
oscillation used by Robin (Proposition 1 of §4 of Robin 1984, cited as Proposition 3.2 in
Lagarias' paper): the singularity of `log ζ` at `ρ` produces, through the explicit formula
for `Σ_{n ≤ x} Λ(n)/(n log n)`, a positive term `≍ x^{b-1}/log x` which dominates the
`x^{-1/2+o(1)}` contributions of the critical-line zeros.

**Status.** Not proved.  The companion *qualitative* statement
`Commons.NumberTheory.Zeta.not_psi_sub_self_bigO_of_zeta_zero`
(`ψ(x) − x` is not `O(x^θ)` for `θ < Re ρ`) is proved in the commons; what is missing is
the sign, the quantitative form, and the passage from `ψ` to the Mertens-3 sum. -/
def MertensErrorOscillationOfZeroOffLine : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → ∃ c : ℝ, MertensErrorOscillation ρ.re c

/-- The conclusion form of Robin's Theorem 2 (Proposition 3.2 of Lagarias' paper):
infinitely many `n` with `σ(n) ≥ e^γ n log log n + C n log log n/(log n)^β`, `β < 1/2`.
This is *literally* the inner statement of the hypothesis `h22` of
`Commons.NumberTheory.Lagarias.riemannHypothesis_iff_lagarias_inequality`. -/
def SigmaOscillation : Prop :=
  ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
    Filter.Frequently (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≥
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
        C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β) Filter.atTop

/-- **AREA 4 (`RobinOscillationOfMertensError`).**

The transfer step of Robin's Theorem 2: if the Mertens-3 error is positive of size
`c x^{b-1}/log x` for arbitrarily large `x` (with `1/2 < b < 1`), then Robin's inequality
fails infinitely often by a relative amount (i.e. `SigmaOscillation`).

Evaluate at `n = lcm(1,…,⌊x⌋)`: then `log n = ψ(⌊x⌋) ≍ x`, while
`σ(n)/n = ∏_{p ≤ x} (1 − p^{−(a_p+1)})/(1 − 1/p) ≥ e^{logRatioSum x} (1 − 2/(√x log x))`;
hence `log(σ(n)/n) − γ − log log n ≥ E(x) − O(1/(√x log x)) ≍ x^{b-1}/log x`, which beats the
required relative excess `(log n)^{-β}` for every `β > 1 − b` (in particular for some
`β < 1/2`).

**Status.** Not proved.  It is purely elementary given (i) `log (lcm(1..⌊x⌋)) = ψ(⌊x⌋)`,
(ii) the elementary Chebyshev bounds `x/2 ≤ ψ(x) ≤ 2x`, (iii) multiplicativity of `σ` and
`σ(p^a)/p^a = (1 − p^{−(a+1)})/(1 − 1/p)`. -/
def RobinOscillationOfMertensError : Prop :=
  ∀ b : ℝ, (1 / 2 : ℝ) < b → b < 1 → ∀ c : ℝ, MertensErrorOscillation b c → SigmaOscillation

end

end Work.RHPlan
