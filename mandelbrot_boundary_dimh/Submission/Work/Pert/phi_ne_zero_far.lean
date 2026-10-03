import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.exists_norm_add_clog_bound

/-!
# `Work.Pert.phi_ne_zero_far`

Shishikura's Appendix A.1/A.4: far out in the sector `QLeft ξ₀` the (perturbed / unperturbed)
Fatou coordinate `φ` never vanishes, uniformly on balls of radius `‖w‖/4` around points `w`
of the sector (as long as those balls stay in the sector).

The point is purely asymptotic: `φ_asymp` says `tau0 (φ w) = w + a log (-w) + b + o(1)`
for `‖w‖ → ∞` in `QLeft ξ₀`, and `‖w + a log (-w) + b‖ → ∞` along the sector
(`Work.Pert.exists_norm_add_clog_bound`: the linear term dominates the logarithmic one).
Since `tau0 x = -1/x` vanishes only at `x = 0`, the asymptotic value forces `φ w ≠ 0`.
-/

namespace Work.Pert

open Filter

/-- Points of `QLeft ξ₀` of large norm: `tau0 (φ w)` is close to `w + a log (-w) + b`, and the
latter is bounded below by `1`.  Hence `φ w ≠ 0`. -/
theorem phi_ne_zero_far {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R ≤ ‖w‖ →
      Metric.ball w (‖w‖ / 4) ⊆ MandelDim.QLeft d.ξ₀ →
      ∀ u ∈ Metric.ball w (‖w‖ / 4), d.φ u ≠ 0 := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  -- the asymptotic of `d.φ*` on the sector
  obtain ⟨R₁, hR₁⟩ := hasym 1 (by norm_num)
  -- coercivity of `u + a * log (-u) + b`
  obtain ⟨R₂, hR₂⟩ := exists_norm_add_clog_bound a b 1 (by norm_num)
  refine ⟨max 1 (max (4 / 3 * (R₁ + 1)) (4 / 3 * R₂)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  have hR1 : 4 / 3 * (R₁ + 1) ≤ max 1 (max (4 / 3 * (R₁ + 1)) (4 / 3 * R₂)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hR2 : 4 / 3 * R₂ ≤ max 1 (max (4 / 3 * (R₁ + 1)) (4 / 3 * R₂)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  intro w hwQ hwR hball u hu
  -- every point of the ball stays far out and in the sector
  have hnorm : 3 * ‖w‖ / 4 ≤ ‖u‖ := by
    have h1 : dist u w < ‖w‖ / 4 := Metric.mem_ball.mp hu
    rw [dist_eq_norm] at h1
    have h2 : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by
      have h := norm_add_le (w - u) u
      rwa [sub_add_cancel] at h
    have h3 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
    linarith
  have hR1w : R₁ < ‖u‖ := by
    have h := le_trans hR1 hwR
    have : R₁ + 1 ≤ 3 * ‖w‖ / 4 := by linarith
    linarith
  have hR2w : R₂ ≤ ‖u‖ := by
    have h := le_trans hR2 hwR
    have : R₂ ≤ 3 * ‖w‖ / 4 := by linarith
    linarith
  have hs := hR₁ u (hball hu) hR1w
  have hb := hR₂ u hR2w
  intro hzero
  have hz : MandelDim.tau0 (d.φ u) = 0 := by rw [hzero]; simp [MandelDim.tau0]
  rw [hz, zero_sub, norm_neg] at hs
  linarith

end Work.Pert
