import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

/-!
# Definitions for the bad-line part of the low-strip seminorm bound

This file collects the definitions used by
`Work.Asymptotics.HalfFunnel.lowRegion_badLine`:

* `lowBadSet` — the region `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2, |Re τ| > 3/4}`;
* `tpole` — the translate pole `(n/2π)/(i t - (τ - n))`, `n = ±1` the sign of `Re τ`;
* `lowT = 3` (a cut beyond all pole heights) and `lowWin` — the spike window
  `(Im τ - 1/8, Im τ + 1/8)`;
* the three pieces `PhiOne`, `PhiTwo`, `PhiSpike` of the Laplace transform
  `Ψ_τ(x) = ∫_0^∞ K(τ,it)e^{-πxt}dt`, with the spike `tpole` removed from the two integrals
  over `(0,1]` and `[1,∞)`;
* `lowF2` — the resulting explicit layer: the three pieces times `2 - 2cos(πr²)` plus the
  paper's `highPart` (`∫_1^∞ 𝒢(τ,it)e^{-πxt}dt` in closed form).
-/

noncomputable section

open MeasureTheory UpperHalfPlane

namespace Work.Asymptotics.HalfFunnel

open Work.Kernels

/-- The region of the low strip near the bad lines `Re τ = ±1`. -/
def lowBadSet : Set ℍ :=
  {τ | τ ∈ Work.Asymptotics.DomainD ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧
    (3 / 4 < τ.re ∨ τ.re < -(3 / 4))}

/-- The sign `n = ±1` of the translate whose pole `z = τ - n` approaches the contour. -/
def tsign (τ : ℍ) : ℝ := if 0 < τ.re then 1 else -1

/-- The translate pole `(n/2π)/(i t - (τ - n))` at the contour point `z = i t`. -/
def tpole (τ : ℍ) (t : ℝ) : ℂ :=
  ((tsign τ : ℂ) / (2 * Real.pi)) /
    ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))

/-- A cut beyond all pole heights: the translate poles have height `Im τ ≤ 2`. -/
def lowT : ℝ := 3

/-- The half-width of the spike window around `t = Im τ`. -/
def lowRho : ℝ := 1 / 8

/-- The spike window `(Im τ - 1/8, Im τ + 1/8)`. -/
def lowWin (τ : ℍ) : Set ℝ := Set.Ioo (τ.im - lowRho) (τ.im + lowRho)

/-- The spike contribution `∫_{lowWin τ} (n/2π)/(i t - (τ-n)) e^{-πxt}dt`. -/
def PhiSpike (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in lowWin τ, tpole τ t * Complex.exp (-(Real.pi * x * t))

/-- The spike-removed low piece `∫_0^{1}(K - pole·1_win)e^{-πxt}dt`. -/
def PhiOne (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioc 0 1,
    (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) *
      Complex.exp (-(Real.pi * x * t))

/-- The spike-removed tail piece `∫_{[1,∞)}(K - Aexp - pole·1_win)e^{-πxt}dt`. -/
def PhiTwo (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (x : ℝ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ),
    (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) *
      Complex.exp (-(Real.pi * x * t))

/-- The explicit candidate layer for the bad-line region. -/
def lowF2 (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ) *
      (PhiOne ℓ d τ (r ^ 2) + PhiTwo ℓ d τ (r ^ 2) + PhiSpike τ (r ^ 2)) +
    highPart (Gcusp ℓ d) τ r

end Work.Asymptotics.HalfFunnel
