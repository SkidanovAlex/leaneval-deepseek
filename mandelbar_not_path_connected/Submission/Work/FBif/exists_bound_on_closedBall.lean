import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

theorem exists_bound_on_closedBall {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ Q := by
  rcases le_or_gt 0 r with hr | hr
  · obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
      ⟨0, by simp [Metric.mem_closedBall, hr]⟩ hf.continuousOn.norm
    refine ⟨‖f x‖, norm_nonneg _, fun z hz => hmax ?_⟩
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hx ⊢
    exact hz
  · exact ⟨0, le_refl 0, fun z hz => absurd hz (by linarith [norm_nonneg z])⟩

end Work.FBif
