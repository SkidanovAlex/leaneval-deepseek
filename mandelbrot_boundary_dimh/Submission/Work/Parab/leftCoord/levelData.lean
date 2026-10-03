import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.wMap_large_estimates

/-!
# The level facts used by the left chart coordinate

The construction of the left chart coordinate `Φ` of a parabolic germ works with a *single*
level `N` at which all the analytic estimates for the chart dynamics `wMap f` and its Fatou
coordinate `ψ = fatouCoordW f (1 - a)` are available.  This file packages those estimates as a
structure `LevelFacts f h a r N`, so that the lemmas about the extension and about the
surjectivity can be stated with `N` as a parameter (the estimates are all of the form
"for `x` with `N < ‖x‖` (or `N < x.re`)", hence monotone in `N`, see `LevelFacts.mono`).

For a parabolic germ with `ParabolicBounds f h a r A A'` such a level exists
(`exists_levelFacts`, proved from the `FatouCoord` library); the level can be enlarged freely.
-/

namespace Work.Parab.leftCoord

open Work.FatouCoord Set Filter Metric
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {f h : ℂ → ℂ} {a : ℂ} {r N N' : ℝ}

/-- The level-`N` facts about the chart dynamics `wMap f` and the Fatou coordinate
`ψ = fatouCoordW f (1 - a)` used in the construction of the left chart coordinate.

All fields have the form "for every `x` with `N < ‖x‖` (or `N < x.re`)" (or `1 / r < N`), so
the structure is monotone in `N` (`LevelFacts.mono`). -/
structure LevelFacts (f h : ℂ → ℂ) (a : ℂ) (r : ℝ) (N : ℝ) : Prop where
  /-- the level is positive -/
  pos : 0 < N
  /-- the level is beyond the disc on which the germ is controlled -/
  hr : 1 / r < N
  /-- the two-term asymptotic of `wMap f`, and the fact that it moves real parts to the right
  by at least `1/2` per step, uniformly in the direction -/
  step : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℂ, N < ‖x‖ →
    ‖wMap f x - (x + 1)‖ ≤ K / ‖x‖ ∧
    ‖wMap f x - (x + 1 + (1 - a) / x)‖ ≤ K / ‖x‖ ^ 2 ∧
    ‖deriv (wMap f) x - 1‖ ≤ K / ‖x‖ ^ 2 ∧
    x.re + 1 / 2 ≤ (wMap f x).re
  /-- `wMap f` is complex differentiable on `{N < ‖·‖}` -/
  gdiff : ∀ x : ℂ, N < ‖x‖ → DifferentiableAt ℂ (wMap f) x
  /-- `wMap f` is injective on `{N < ‖·‖}` -/
  ginj : Set.InjOn (wMap f) {x : ℂ | N < ‖x‖}
  /-- the Abel equation for `ψ` on the half-plane `{Re > N}` -/
  abel : ∀ x : ℂ, N < x.re → fatouCoordW f (1 - a) (wMap f x) = fatouCoordW f (1 - a) x + 1
  /-- `ψ` is holomorphic on `{Re > N}` -/
  ψdiff : DifferentiableOn ℂ (fatouCoordW f (1 - a)) {x : ℂ | N < x.re}
  /-- `ψ` is injective on `{Re > N}` -/
  ψinj : Set.InjOn (fatouCoordW f (1 - a)) {x : ℂ | N < x.re}
  /-- the derivative of `ψ` is close to `1` on `{Re > N}` -/
  deriv_close : ∀ x : ℂ, N < x.re → ‖deriv (fatouCoordW f (1 - a)) x - 1‖ ≤ 1 / 2
  /-- the quantitative remainder `ψ w = w - (1 - a) log w + O(1/Re w)` -/
  rem : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, N < w.re →
    ‖fatouCoordW f (1 - a) w - approxCoord (1 - a) w‖ ≤ K / w.re

/-- The level facts are monotone in the level. -/
theorem LevelFacts.mono {f h : ℂ → ℂ} {a : ℂ} {r N N' : ℝ}
    (hL : LevelFacts f h a r N) (hN : N ≤ N') : LevelFacts f h a r N' where
  pos := lt_of_lt_of_le hL.pos hN
  hr := lt_of_lt_of_le hL.hr hN
  step := by
    obtain ⟨K, hK, hs⟩ := hL.step
    exact ⟨K, hK, fun x hx => hs x (lt_of_le_of_lt hN hx)⟩
  gdiff := fun x hx => hL.gdiff x (lt_of_le_of_lt hN hx)
  ginj := hL.ginj.mono fun x hx => lt_of_le_of_lt hN hx
  abel := fun x hx => hL.abel x (lt_of_le_of_lt hN hx)
  ψdiff := hL.ψdiff.mono fun x hx => lt_of_le_of_lt hN hx
  ψinj := hL.ψinj.mono fun x hx => lt_of_le_of_lt hN hx
  deriv_close := fun x hx => hL.deriv_close x (lt_of_le_of_lt hN hx)
  rem := by
    obtain ⟨K, hK, hs⟩ := hL.rem
    exact ⟨K, hK, fun w hw => hs w (lt_of_le_of_lt hN hw)⟩

end Work.Parab.leftCoord
