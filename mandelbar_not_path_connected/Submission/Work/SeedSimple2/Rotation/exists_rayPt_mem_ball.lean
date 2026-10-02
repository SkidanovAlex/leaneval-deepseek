/-
# SeedSimple2 — a landing ray meets every neighbourhood of its landing point

If the ray of angle `θ` lands at `y` (`Work.EL.LandsN hN θ y`, i.e. the ray points of level
`t → 1⁺` converge to `y`), then for every `ρ > 0` there is a level `t > 1` with the ray point
`rayPt hN θ t` inside the ball of radius `ρ` about `y`.

The content is purely the meaning of convergence of the ray germ: the filter
`nhdsWithin 1 (Ioi 1)` is non-trivial (it contains `Ioi 1` itself), so the preimage of any
neighbourhood of `y` which belongs to it is nonempty, and intersecting it with `Ioi 1` produces
a level `t > 1`.
-/
import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.Rotation

/-- **A landing ray enters every ball around its landing point.** -/
theorem exists_rayPt_mem_ball {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : ℝ, 1 < t ∧ Work.EL.rayPt hN θ t ∈ Metric.ball y ρ := by
  have hball : Metric.ball y ρ ∈ nhds y := Metric.ball_mem_nhds y hρ
  have hpre : (fun t : ℝ => Work.EL.rayPt hN θ t) ⁻¹' Metric.ball y ρ ∈
      nhdsWithin (1 : ℝ) (Set.Ioi 1) := h hball
  have hI : Set.Ioi (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := self_mem_nhdsWithin
  obtain ⟨t, ht, htI⟩ := Filter.nonempty_of_mem (Filter.inter_mem hpre hI)
  exact ⟨t, htI, ht⟩

end Work.SeedSimple2.Rotation
