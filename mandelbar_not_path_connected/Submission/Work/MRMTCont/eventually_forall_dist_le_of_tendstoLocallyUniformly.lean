import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMTCont

open Filter

/-- If, for every `j`, the sequence of functions `F j ·` converges locally uniformly to `g j`,
then on the closed disc of radius `j` the convergence is eventually uniform with the explicit
error bound `1 / (j + 1)`.  This uses that locally uniform convergence on the locally compact
space `ℂ` implies uniform convergence on every compact set, and that the closed disc
`Metric.closedBall 0 j` is compact. -/
theorem eventually_forall_dist_le_of_tendstoLocallyUniformly {F : ℕ → ℕ → ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (h : ∀ j, TendstoLocallyUniformly (F j) (g j) Filter.atTop) (j : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z : ℂ, ‖z‖ ≤ (j : ℝ) → dist (F j n z) (g j z) ≤ 1 / ((j : ℝ) + 1) := by
  have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (j : ℝ)) := isCompact_closedBall _ _
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp (h j)) _ hK
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity] at hu
  filter_upwards [hu (1 / ((j : ℝ) + 1)) hε] with n hn
  intro z hz
  rw [dist_comm]
  exact hn z (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz)

end Work.MRMTCont
