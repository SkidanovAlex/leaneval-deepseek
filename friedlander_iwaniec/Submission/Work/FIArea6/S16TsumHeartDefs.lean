/-
# `Submission.Work.FIArea6.S16TsumHeartDefs` — the §16 heart, as a reusable `Prop`

*FI* §16 bounds the character sum `S_χ^k(β)` of (16.25) by first Fourier-expanding `q` and
Mellin-inverting `p` ((16.26)–(16.29)), which reduces it to the *Möbius-twisted Hecke sum*

  `Tsum = Σ_n 1_{(n,Π)=1}·λ_m(n)·μ(n)·γ(n;C)·p(n)`

of (16.30) — the inner Dirichlet-type sum whose contour shift (16.31)–(16.38) is the analytic
heart of §16.  This module isolates that heart as a single `Prop`, `S16TsumHeart`, so that it can
be delegated and consumed independently of the Frobenius/Fourier bookkeeping of (16.25)–(16.29).

The statement is *FI* (16.38) with the two constants of the printed Lemma 16.2 (`c` in the
exponent, `C` as the implied constant), and with the modulus allowance `d ≤ 2(log N)^ν` (the
factor `2` is what the (5.7) character detection of §16 costs).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FIArea5.S16.fourier_truncation
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The §16 heart (*FI* (16.38)) for the Möbius-twisted Hecke sum `Tsum`.**

For every `ε ∈ (0,1/4]` there are `c, C, x0 > 0` such that for every admissible datum `Pa` with
`x0 ≤ Pa.x`, every `ν < 1/(2ε)`, every `d ≥ 1` with `d ≤ 2(log N)^ν`, every frequency
`|m| ≤ 4exp(√log N)` (this must absorb the incoming frequency `|j| ≤ 3exp(√log N)` of
`S16CleanCoreTwo` together with the Fourier range `|ℓ| ≤ exp(√log N)` of (16.27)), every strict character `χ` mod `4d` and every mollifier `p` of the class
(4.12)/(4.14),

  `‖Tsum Pa χ m p‖ ≤ C[exp(-ηc(4d)^{-ε}√log N) + exp(-η log N/log Pz)]·(4d)N(log N)^6`.

This is the contour-shift bound (16.36)–(16.38) applied to
`Tsum = Σ_n 1_{(n,Π)=1}λ_m(n)μ(n)γ(n;C)p(n)`: the Euler-product regrouping
`Z = M·P·Q` of (16.30)–(16.35), with (16.31) `M(s) ≪ d log²` from the inverse bound
`HeckeLcontInvBoundAll` ((16.23)/(16.24)), (16.33) `P(s) ≪ (log Pz)³`, (16.34)
`Q(s) ≪ C^{1-σ}log C`, and the shift `δ = min{c_h/(d^ε log T), 1/log Pz}` at height
`T = 3exp(√log N)`.

The two constants are *independent* — precisely the paper's printed Lemma 16.2 — so this cannot be
obtained by scaling. -/
def S16TsumHeart : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (ν : ℝ) (d : ℕ) (m : ℤ) (chi : GaussianInt → ℂ) (p : ℝ → ℝ),
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ 2 * (Real.log Pa.N) ^ ν →
      |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ContDiff ℝ 2 p → (∀ u, 0 ≤ p u) → (∀ u, p u ≤ 1) →
      (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) →
      (∀ k : ℕ, k ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv k p u| ≤ Work.FITop4.cMoll k * (Pa.θ * Pa.N) ^ (-(k : ℝ))) →
      ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
        ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- The *clean §16 summand* `p(|z|²)·μ(|z|²)·γ(|z|²;C)·ψ_m(z)` on the support
`IsPrimary z ∧ NoSmallPrimes Pa z`, and `0` off it.  (Written as a `def` so that the statements of
the lemmas about it elaborate without a local `propDecidable` instance.) -/
def S16CleanSummand (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (z : GaussianInt) : ℂ := by
  classical
  exact
    if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
      (p (Work.FIPlan.gnorm z) : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
        * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
        * Work.FIArea5.S16Hecke.psi chi m z
    else 0

end

end Work.FIArea6
