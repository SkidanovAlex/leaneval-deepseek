import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Core

open Function

/-- If `pMap c` maps the closed exterior of the disk of radius `R` into itself in
the strong sense that both the norm and the distance from the origin grow, then
every orbit starting at `‖z‖ ≥ R` stays outside that disk and moves monotonically
away from the origin. -/
theorem norm_iterate_pMap_ge (c : ℂ) (R : ℝ)
    (hR : ∀ w : ℂ, R ≤ ‖w‖ → R ≤ ‖Work.Bottcher.pMap c w‖ ∧ ‖w‖ ≤ ‖Work.Bottcher.pMap c w‖)
    (z : ℂ) (hz : R ≤ ‖z‖) (n : ℕ) :
    R ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ ∧ ‖z‖ ≤ ‖(Work.Bottcher.pMap c)^[n] z‖ := by
  induction n with
  | zero => exact ⟨hz, le_refl ‖z‖⟩
  | succ n ih =>
    rw [iterate_succ_apply']
    obtain ⟨h1, h2⟩ := hR _ ih.1
    exact ⟨h1, ih.2.trans h2⟩

end Work.Bottcher.Core
