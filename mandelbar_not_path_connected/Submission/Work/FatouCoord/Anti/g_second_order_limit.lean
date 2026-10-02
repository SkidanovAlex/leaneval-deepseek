import Mathlib
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Anti

/-- Second-order expansion of an anti-holomorphic germ which is a first-order approximation to
the reflection `z ↦ star z`.  If `z ↦ star (g z)` is holomorphic on a disc of radius `r > 0`
around `0`, vanishes at `0`, and `g z = star z + O(|z|^2)` on that disc, then
`(star (g z) - z) / z ^ 2` extends continuously (indeed holomorphically) at `0`; equivalently
`star (g z) = z + b * z ^ 2 + o(z ^ 2)`.

This is the `w`-chart second order statement used to compare an anti-equivariant Fatou coordinate
with the holomorphic one. -/
theorem g_second_order_limit {g : ℂ → ℂ} {r G : ℝ} (hr : 0 < r) (hg_anti : ∀ z ∈ Metric.ball 0 r, DifferentiableAt ℂ (fun z => star (g z)) z) (hg0 : g 0 = 0) (hg_lin : ∀ z ∈ Metric.ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2) : ∃ b : ℂ, Filter.Tendsto (fun z : ℂ => (star (g z) - z) / z ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds b) := by
  set h : ℂ → ℂ := fun z => star (g z) with hh
  set F : ℂ → ℂ := fun z => (h z - z) / z ^ 2 with hF
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) := fun z hz => (hg_anti z hz).differentiableWithinAt
  have hF0 : F 0 = 0 := by
    simp [hF, hh, hg0]
  have hdiff : ∀ᶠ z in nhdsWithin (0:ℂ) {0}ᶜ, DifferentiableAt ℂ F z := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz hz0
    have hdz : DifferentiableAt ℂ h z := hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hzsq : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
    have hq : DifferentiableAt ℂ (fun w : ℂ => (h w - w) / w ^ 2) z :=
      (hdz.sub differentiableAt_id).div (differentiableAt_id.pow 2) hzsq
    simpa [hF] using hq
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) (nhdsWithin (0:ℂ) {0}ᶜ) fun z => ‖F z - F 0‖ := by
    refine ⟨G, ?_⟩
    change ∀ᶠ z in nhdsWithin (0:ℂ) {0}ᶜ, ‖F z - F 0‖ ≤ G
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz hz0
    rw [hF0, sub_zero]
    have hz2 : 0 < ‖z‖ ^ 2 := by
      have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      positivity
    have hstar : h z - z = star (g z - star z) := by
      rw [hh]; simp
    have hn : ‖h z - z‖ = ‖g z - star z‖ := by rw [hstar, norm_star]
    calc ‖F z‖ = ‖h z - z‖ / ‖z ^ 2‖ := by rw [hF]; exact norm_div _ _
      _ = ‖g z - star z‖ / ‖z‖ ^ 2 := by rw [hn, norm_pow]
      _ ≤ (G * ‖z‖ ^ 2) / ‖z‖ ^ 2 := by gcongr; exact hg_lin z hz
      _ = G := by rw [mul_div_assoc, div_self (ne_of_gt hz2), mul_one]
  refine ⟨(nhdsWithin (0:ℂ) {0}ᶜ).limUnder F, ?_⟩
  have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hdiff hbdd
  simpa [hF, hh] using hlim

end Work.FatouCoord.Anti
