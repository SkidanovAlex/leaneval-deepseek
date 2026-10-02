import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Classical Filter Set
open scoped Topology

/-- Every parameter ray of the Nakane interface is unbounded: for each `n` it contains a point
of norm at least `n`.

Indeed, the potential is continuous and `potential (rayPt θ t) = log t`, which is unbounded
along the ray.  If the whole ray were contained in the compact ball `closedBall 0 n`, the
potential — continuous and hence bounded on that ball — would be bounded along the ray,
contradiction. -/
theorem paramRay_unbounded {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) (n : ℕ) :
    ∃ c ∈ Work.Top.NakaneData.paramRay hN θ, (n : ℝ) ≤ ‖c‖ := by
  -- The potential attains a maximum `M` on the compact ball of radius `n`.
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (n : ℝ)) := isCompact_closedBall 0 (n : ℝ)
  have hne : (Metric.closedBall (0 : ℂ) (n : ℝ)).Nonempty :=
    ⟨0, by simp [Metric.mem_closedBall]⟩
  obtain ⟨x, _hxmem, hxmax⟩ := hK.exists_isMaxOn hne hN.continuous_potential.continuousOn
  set M : ℝ := Work.Top.potential Mb Φ x with _hM
  have hMbound : ∀ y ∈ Metric.closedBall (0 : ℂ) (n : ℝ), Work.Top.potential Mb Φ y ≤ M :=
    fun y hy => hxmax hy
  -- Take the ray point of level `exp (|M| + 1)`, whose potential is `|M| + 1 > M`.
  have ht : 1 < Real.exp (|M| + 1) := by
    rw [Real.one_lt_exp_iff]; positivity
  refine ⟨hN.rayPt θ (Real.exp (|M| + 1)), ?_, ?_⟩
  · rw [Work.Top.NakaneData.paramRay_eq_range]
    exact ⟨⟨Real.exp (|M| + 1), ht⟩, rfl⟩
  · rw [← not_lt]
    intro hlt
    have hmem : hN.rayPt θ (Real.exp (|M| + 1)) ∈ Metric.closedBall (0 : ℂ) (n : ℝ) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hlt
    have hle := hMbound _ hmem
    have hpot := Work.Top.NakaneData.potential_rayPt hN (θ := θ) ht
    rw [hpot, Real.log_exp] at hle
    have habs : M < |M| + 1 := by have := le_abs_self M; linarith
    linarith

end Work.Top
