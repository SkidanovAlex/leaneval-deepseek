import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-- A continuous map `F : ℂ → ℂ` that eventually grows at least linearly along every direction
(`2 * ‖z‖ ≤ ‖F z‖` for all `‖z‖ ≥ R`) is proper: preimages of compact sets are compact.

Indeed, for a compact `K` the image bound `‖F z‖ ≤ M` on `K`, together with the escape bound,
forces `F ⁻¹' K` to lie in the compact ball of radius `max R M`; the preimage is also closed. -/
theorem isProperMap_of_escapeBound {F : ℂ → ℂ} (hF : Continuous F)
    (hesc : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖F z‖) : IsProperMap F := by
  obtain ⟨R, hRpos, hR⟩ := hesc
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hF, fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  refine (isCompact_closedBall (0 : ℂ) (max R M)).of_isClosed_subset
    (hK.isClosed.preimage hF) (fun z hz => ?_)
  have hFz : ‖F z‖ ≤ M := by
    have := hM hz
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_cases hzR : R ≤ ‖z‖
  · have h2 : 2 * ‖z‖ ≤ M := le_trans (hR z hzR) hFz
    have : ‖z‖ ≤ M := by linarith [norm_nonneg z]
    exact le_trans this (le_max_right _ _)
  · have hzlt : ‖z‖ < R := lt_of_not_ge hzR
    exact le_trans (le_of_lt hzlt) (le_max_left _ _)

end Work.FatouParabolic.Core
