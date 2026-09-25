import ChallengeDeps
import Submission.Work.RHPlan.Defs
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Mathlib.NumberTheory.Chebyshev

/-!
# `Work.RHContract.Defs` — the vocabulary of the replacement contract

This module fixes the language of the route of `Submission/Work/RHPlan/ROUTE_LEAD.md`:

* `kW` is the kernel `k(t) = (1 + log t)/(t² log² t)`;
* `psiTail x` is `J(x) = ∫_x^∞ (ψ t − t) k(t) dt`, the *same integrand* as the corpus theorem
  `Commons.NumberTheory.Zeta.psi_integral_lower_bound_explicit`;
* `primeTail x` is the (nonnegative) tail `Σ_{p ≤ x} Σ_{k > e_p} 1/(k p^k)` of the Mertens-3
  logarithmic sum, `e_p = ⌊log x / log p⌋` being the exponent of `p` in `lcm(1..⌊x⌋)`.

The three areas of the replacement contract are:

* `RobinCAFrom1530`   — AREA A: Robin's inequality at CA numbers with `ξ(ε) ≥ 1530`
                        (regions I, II, III of ROUTE_LEAD §2; `ξ < 1530` is the *proved*
                        commons theorem `Robin.robin_caFval_small`);
* `LandauInput`       — AREA B1: `¬RH` forces the oscillation `PsiTailOscillation` of `J`;
* `TransferInput`     — AREA B2: that oscillation of `J` forces `SigmaOscillation`.

The vocabulary of `Submission.Work.RHPlan.Defs` (`RobinBound`, `caNumber`, `caSupport`,
`caXi`, `caMu`, `IsColossallyAbundant`, `SigmaOscillation`, …) is reused by import; the
composition `rh_iff_of_areas'` lives in `Work.RHContract.Interfaces`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

open MeasureTheory

/-! ## The kernel and the two tails -/

/-- The kernel `k(t) = (log t + 1)/(t² log² t)` of the `J`-integral. -/
def kW (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)

/-- `J(x) = ∫_x^∞ (ψ t − t) k(t) dt`: the `ψ`-tail of the Mertens-3 identity.

This is the `J` of ROUTE_LEAD §1.  It is the same integral (same integrand, same range) as
the one bounded in `Commons.NumberTheory.Zeta.psi_integral_lower_bound_explicit`. -/
def psiTail (x : ℝ) : ℝ := ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * kW t

/-- The prime tail `Σ_{p ≤ x} Σ_{k > e_p} 1/(k p^k)`, where `e_p = ⌊log x / log p⌋` is the
exponent of `p` in `lcm(1..⌊x⌋)`.

The inner sum rewrites the tail of `−log(1 − 1/p) = Σ_{k ≥ 1} 1/(k p^k)`: the terms kept are
exactly those with `k > e_p`. -/
def primeTail (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊,
    (-Real.log (1 - 1 / (p : ℝ)) -
      ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), 1 / ((k : ℝ) * (p : ℝ) ^ k))

/-- The one-sided excess of the `k = e_p + 1` term: `primeTail x ≥ 0` is the assertion that
each summand is `≥ 0`. -/
def primeTailSummand (p : ℕ) (x : ℝ) : ℝ :=
  -Real.log (1 - 1 / (p : ℝ)) -
    ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), 1 / ((k : ℝ) * (p : ℝ) ^ k)

lemma primeTail_eq_sum (x : ℝ) :
    primeTail x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, primeTailSummand p x := rfl

/-! ## AREA A — Robin at CA numbers with `ξ ≥ 1530` -/

/-- **AREA A (`RobinCAFrom1530`).**  Under `RH`, Robin's inequality holds at every colossally
abundant number `N_ε` whose largest prime factor satisfies `ξ(ε) ≥ 1530`.

This is the honest remainder of Robin's Theorem 1 after the commons theorem
`Robin.robin_caFval_small` (which covers `ξ(ε) < 1530`).  ROUTE_LEAD §2 splits it into
Region I (`1530 ≤ ξ < 3·10^4`, certified), Region II (`3·10^4 ≤ ξ < 10^8`, q-certificate) and
Region III (`10^8 ≤ ξ`, pure analysis). -/
def RobinCAFrom1530 : Prop :=
  RiemannHypothesis → ∀ ε : ℝ, 0 < ε → (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) →
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε)

/-! ## AREA B1 — Landau: an off-line zero makes `J` very negative infinitely often -/

/-- **AREA B1 conclusion (`PsiTailOscillation`).**  There is a `β ∈ (0, 1/2)` such that
`J(x) ≤ −2 x^{−β}` for arbitrarily large `x`.  (This is what a single off-line zero of `ζ`
produces through the Mellin/Landau argument of ROUTE_LEAD §3.3.) -/
def PsiTailOscillation : Prop :=
  ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ ∀ x₀ : ℝ, ∃ x : ℝ, x₀ ≤ x ∧ psiTail x ≤ -2 * x ^ (-β)

/-- **AREA B1 (`LandauInput`).**  `¬RH → PsiTailOscillation`: an off-line zero of `ζ` forces
the oscillation of `J`.  This is ROUTE_LEAD §3.3, lemmas B2–B7. -/
def LandauInput : Prop := ¬ RiemannHypothesis → PsiTailOscillation

/-! ## AREA B2 — the elementary transfer at `n = lcm(1..⌊x⌋)` -/

/-- **AREA B2 (`TransferInput`).**  The oscillation of `J` transfers to Robin counterexamples
(`SigmaOscillation`), by evaluating at `n = lcm(1..⌊x⌋)`: ROUTE_LEAD §3.1, Lemma T. -/
def TransferInput : Prop := PsiTailOscillation → Work.RHPlan.SigmaOscillation

end

end Work.RHContract
