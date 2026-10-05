import Mathlib
import Submission.Work.RPV.Defs

/-!
# RPB1a: the analytic (conformal-map) route to `B1` — vocabulary

This is the definition file of subproject `Submission/Work/RPB1a/` (namespace `Work.RPB1a`),
the analytic route to node B1 `Work.RPB.B1.exists_curveIsotopy` designed in
`RECTPEG_B1_LEAD.md` (session curric-46, 2026-10-05).

The five notions below are copied verbatim from `RECTPEG_B1_STATEMENTS.lean.txt` (namespaces
aside: the design used `Work.RPB.B1a`, this directory uses `Work.RPB1a`).  Everything in the
subproject is stated in terms of them, so they are the shared vocabulary; **do not redeclare**
them, import this module.

* `IsSmoothLoop u` — `u : ℝ → ℂ` is `C^∞`, `2π`-periodic, injective mod `2π`, immersed.
  This is the image of a smooth embedded circle under the parametrisation `t ↦ e^{it}`.
* `IsLoopFamily c` — the four non-normalisation fields of `Work.RPV.CurveIsotopy`: jointly `C^∞`,
  `2π`-periodic, and embedded/immersed on the parameter range `s ∈ [0,1]`.
* `trigPoly N a` — the trigonometric polynomial `∑_{|n| ≤ N} a n e^{int}`.
* `laurentPoly N a` — the Laurent polynomial `∑_{|n| ≤ N} a n w^n`; restricted to the unit circle
  it *is* `trigPoly` (`laurentPoly_exp`).
* `annulus ρ` — the inversion-symmetric annulus `ρ < |w| < ρ⁻¹`, the collar of the unit circle on
  which a trigonometric loop is locally injective with non-vanishing derivative.

The shared route vocabulary (`Work.RPV.CurveIsotopy`, `Work.RPV.IsSmoothJordan`, `Work.RPV.ωC`)
lives in `Submission.Work.RPV.Defs` and is imported, never redefined.
-/

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real

noncomputable section

namespace Work.RPB1a

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

end Work.RPB1a

end
