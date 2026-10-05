import Mathlib
import Submission.Work.RPV.Defs

/-!
# `Work.RPB.B1a`: the conformal-map route for the curve isotopy (B1)

Definitions for the route designed in `RECTPEG_B1_LEAD.md` (2026-10-05).  This file contains **only
definitions**: it is the vocabulary that the B1a nodes (`Submission/Work/RPB/B1a/*`) speak about.

* `IsSmoothLoop u`: a `C^∞`, `2π`-periodic, injective-mod-`2π`, immersed loop in `ℂ`;
* `IsLoopFamily c`: a jointly `C^∞` family of such loops, embedded and immersed for `s ∈ [0,1]`
  (exactly the four non-normalisation fields of `Work.RPV.CurveIsotopy`);
* `trigPoly N a t = ∑_{|n| ≤ N} a n e^{int}`: a trigonometric polynomial;
* `laurentPoly N a w = ∑_{|n| ≤ N} a n w^n`: its Laurent form, so that
  `laurentPoly N a (exp (t * I)) = trigPoly N a t`;
* `annulus ρ = {ρ < ‖w‖ < ρ⁻¹}`: the inversion-symmetric annulus.
-/

open Complex Set Metric
open scoped ContDiff Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

/-- A `C^∞`, `2π`-periodic, injective-mod-`2π`, immersed loop in `ℂ`. -/
def IsSmoothLoop (u : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ t, u (t + 2 * π) = u t) ∧
  (∀ t t', u t = u t' → ∃ m : ℤ, t' = t + 2 * π * m) ∧ (∀ t, deriv u t ≠ 0)

/-- A jointly `C^∞` family of `2π`-periodic loops, embedded and immersed for `s ∈ [0,1]`
(exactly the four non-normalisation fields of `Work.RPV.CurveIsotopy`). -/
def IsLoopFamily (c : ℝ → ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2) ∧ (∀ s t, c s (t + 2 * π) = c s t) ∧
  (∀ s ∈ Icc (0 : ℝ) 1, ∀ t t', c s t = c s t' → ∃ m : ℤ, t' = t + 2 * π * m) ∧
  (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, deriv (c s) t ≠ 0)

/-- Trigonometric polynomial `∑_{|n| ≤ N} a n e^{int}`. -/
def trigPoly (N : ℕ) (a : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * Complex.exp ((n : ℂ) * (t : ℂ) * I)

/-- The Laurent polynomial `∑_{|n| ≤ N} a n w^n`, so that `laurentPoly N a (e^{it}) = trigPoly N a t`. -/
def laurentPoly (N : ℕ) (a : ℤ → ℂ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * w ^ n

/-- The inversion-symmetric annulus `ρ < |w| < 1/ρ`. -/
def annulus (ρ : ℝ) : Set ℂ := {w | ρ < ‖w‖ ∧ ‖w‖ < ρ⁻¹}

end Work.RPB.B1a
