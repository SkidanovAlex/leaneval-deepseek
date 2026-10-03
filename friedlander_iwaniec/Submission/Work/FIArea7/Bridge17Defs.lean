/-
# `Submission.Work.FIArea7.Bridge17Defs` — the vocabulary of the *FI* §17 bridge

The bridge of *FI* §17 turns the round-6 coefficient `β` of `IsBetaCoeff6` — which carries the
*angle mollifier* `q(arg z − φ)` (5.12), the class condition `SameClass8 z z0` (5.7) and the
divisor condition `τ(|z|²) ≤ Pa.τ` (5.9) inside its support — into the coefficient (17.15) for which
Proposition 17.2 (`Work.FIArea7.Prop172Classical`) is stated:

* `q` is expanded in its Fourier series (16.26)–(16.27), truncating at `L = modeLen Pa X`;
* `SameClass8` is detected by characters to modulus eight (`sameClass8_decomp`, *FI* p. 1009);
* (5.9) is removed by a Rankin mass bound (`deltaTau_mass_le`), *FI* (10.4);
* `IsAxisFree` is a *hypothesis* of the amended round-6 contract `Work.FITop4.Area7_6b`.

The definitions here are those of `AREA7_ROUTE_LEAD.md` §2.2.  See `NOTES.md` §61 and
`AREA7_ROUTE_LEAD.md` for the route.
-/
import Mathlib
import Submission.Work.FIArea7.Prop172Classical
import Submission.Work.FIArea7.AngFourier
import Submission.Work.FITop4.Areas6c

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The two mollifiers of (5.12)/(4.13) as they occur in the bridge: an angular `q` of width
`2πθ` with the `C²`/`θ^{-j}` bounds and a radial `p` supported on the annulus (4.12) with the
`C²`/`(θN)^{-j}` bounds.  This is exactly the pair of clauses that `IsBetaCoeff6` produces, and
exactly the hypothesis class of `Prop172Classical`'s radial weight. -/
def IsMollPair (Pa : Work.FITop.Params) (q p : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 q ∧ ContDiff ℝ 2 p ∧
  (∀ α, 0 ≤ q α ∧ q α ≤ 1) ∧
  (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) ∧
  (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ,
    |iteratedDeriv j q α| ≤ Work.FITop4.cMoll j * Pa.θ ^ (-(j : ℝ))) ∧
  (∀ u, 0 ≤ p u ∧ p u ≤ 1) ∧
  (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
  (∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
    |iteratedDeriv j p u| ≤ Work.FITop4.cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ)))

/-- `radBeta` restricted to one class modulo eight: the (5.7) support of the round-6 coefficient. -/
def radBetaCls (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z0 z : GaussianInt) : ℂ :=
  (if Work.FITop4.SameClass8 z z0 then 1 else 0) * Work.FIArea7.radBeta Pa p Pa.C z

/-- The truncated Fourier series of the angle mollifier `q` at the angle `α` — *FI* (16.27). -/
def angTruncSum (q : ℝ → ℝ) (L : ℕ) (α : ℝ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L,
    Work.FIArea7.angFourierCoeff (fun t => ((q t : ℝ) : ℂ)) ℓ
      * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))

/-- The round-6 coefficient **as a function of the angle**, with its support restrictions
`InPolarBox`, `NoSmallPrimes`, `SameClass8` (5.7) — but *without* the divisor condition (5.9) and
without `IsAxisFree` (which is a contract hypothesis of `Area7_6b`).  This is *FI* (5.13) with the
angle written explicitly; the sector support is carried by `q`. -/
def betaTilde (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (φ : ℝ) (z0 z : GaussianInt) : ℂ :=
  ((q (Complex.arg z.toComplex - φ) : ℝ) : ℂ) * radBetaCls Pa p z0 z

/-- The (17.15)/(16.29) coefficient: the angle mollifier replaced by its truncated Fourier series,
so that the deep input can be applied at the *shifted* frequencies `k+ℓ`. -/
def betaL (Pa : Work.FITop.Params) (q p : ℝ → ℝ) (φ : ℝ) (z0 : GaussianInt) (L : ℕ)
    (z : GaussianInt) : ℂ :=
  angTruncSum q L (Complex.arg z.toComplex - φ) * radBetaCls Pa p z0 z

/-- **The mode length** of the §17 bridge (replaces `Work.FIArea7.angModeLen` and
`angModeLen2 = X²+2`).  Two effects force it:

* the truncation error of (16.27) lives on the *whole annulus* (the truncated series does not
  vanish off the sector) and the coefficient is `≪ τ(n)`, not `≪ 1`, so its `L²`-mass is
  `≍ θ⁻²L⁻²·N·polylog` (`deltaQ_mass_le`): this gives the factor `θ⁻¹·X·log⁶N`;
* the character has to be doubled to the modulus `lcm(Q,8)`, absorbed by the factor `2` in the
  region split's slack `L₀' = 2K + 2·modeLen Pa X + 2`.

In the composition's regime `Pa.θ⁻¹ = (log x)^{201048576}` and `X ≤ (log N)^{nuU}`, so `modeLen` is
a polylogarithm (and `area7_small_theta` handles the trivial complement). -/
def modeLen (Pa : Work.FITop.Params) (X : ℕ) : ℕ :=
  Nat.ceil Pa.θ⁻¹ * X * Nat.ceil (Real.log (Pa.N + 2)) ^ 6

end

end Work.FIArea7
