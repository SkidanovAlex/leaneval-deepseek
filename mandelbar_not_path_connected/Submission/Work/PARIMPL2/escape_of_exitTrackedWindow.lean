/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.escape_of_exitTrackedWindow` — the tracked exit escapes the mandelbar

The **escape** half of the leak: from

* the tracked bounded-window exit `Work.PARIMPL2.ExitTrackedWindow` of the transit (a point of the
  critical orbit of `c` sits within any prescribed `η` of `Ψ` at every admissible transit level
  `trans c + k` in a bounded window `−Xo ≤ · < −1`),
* the robustness `hrob` of the leak disc (near `c₀` nothing within `ρ` of `Ψ '' closedBall x r`
  lies in the filled Julia set `K c`),

a parameter `c ∈ Nm` near `c₀` whose transit coordinate lands on the leak level `x` modulo `ℤ`
(`distZ (trans c) x < r/2`) cannot be in the mandelbar: the exit produces a point `(Ft c)^[n] c`
of the critical orbit within `ρ` of `Ψ u` with `u = trans c + k ∈ closedBall x r`, so that point
is **outside** `K c`, while the critical orbit of a mandelbar parameter is bounded — a
contradiction.  The two ingredients are `Work.GATE2.ExitTrackedLoc` (which
`ExitTrackedWindow` is, up to binder order) and `Work.GATE2.Escape.escape_of_robust` together
with the extraction of the integer from `distZ`
(`Work.GATE2.exists_dist_lt_of_distZ_lt`).

This is exactly the `escape` field of `Work.PARIMPL.LeakData` (and of
`Work.PARIMPL2.LeakData`), obtained from the repaired exit tracking instead of being assumed.
-/
import Mathlib
import Submission.Work.PARIMPL2.ExitTracking
import Submission.Work.GATE2.Escape.escape_of_robust

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2

/-- `Work.PARIMPL2.ExitTrackedWindow` is the same statement as `Work.GATE2.ExitTrackedLoc` (the
only difference is the order in which the window half-width `Xo` and the accuracy `η` are
introduced). -/
theorem exitTrackedLoc_of_exitTrackedWindow {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ}
    {Ft : ℂ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    (hw : Work.PARIMPL2.ExitTrackedWindow c₀ Nm trans Ft Ψ) :
    Work.GATE2.ExitTrackedLoc c₀ Nm trans Ft Ψ :=
  fun X η hX hη => hw X hX η hη

theorem escape_of_exitTrackedWindow {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {Ft : ℂ → ℂ → ℂ}
    {Ψ : ℂ → ℂ} {x r : ℝ}
    (hw : Work.PARIMPL2.ExitTrackedWindow c₀ Nm trans Ft Ψ)
    (hr : 0 < r)
    (hcont : Continuous Ψ)
    (hFt : ∀ c, Ft c = Work.EL.F c)
    (hx : x + r / 2 < -1)
    (hrob : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Metric.ball c₀ ρ, ∀ y : ℂ,
      (∃ z ∈ Metric.closedBall ((x : ℝ) : ℂ) r, dist y (Ψ z) ≤ ρ) → y ∉ Work.EL.K c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ Nm ∩ Metric.ball c₀ ρ,
      Work.PARIMPL.distZ (trans c) ((x : ℝ) : ℂ) < r / 2 →
        c ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  have hExit : Work.GATE2.ExitTrackedLoc c₀ Nm trans Ft Ψ :=
    exitTrackedLoc_of_exitTrackedWindow hw
  have hx' : (((x : ℝ) : ℂ)).re + r / 2 < -1 := by simpa using hx
  obtain ⟨ρ, hρ, hesc⟩ :=
    Work.GATE2.Escape.escape_of_robust (x := ((x : ℝ) : ℂ)) hr hcont hFt hx' hrob hExit
  refine ⟨ρ, hρ, fun c hc hZ => ?_⟩
  obtain ⟨k, hk⟩ := Work.GATE2.exists_dist_lt_of_distZ_lt hZ
  exact hesc c hc k hk

end Work.PARIMPL2
