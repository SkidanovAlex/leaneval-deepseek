/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A holomorphic function with `G 0 = 0`, `G'(0) = 1` is tangent to the identity to second order

If `G` is holomorphic near `0` with `G 0 = 0` and `G'(0) = 1`, then
`star (G u) - star u = O(u ^ 2)`: the antiholomorphic map `u ↦ star (G u)` is tangent to
conjugation.
-/

open scoped Topology
open Filter Metric

namespace Work.FatouCoord.Flower

noncomputable section

theorem norm_star_sub_le {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hG1 : deriv G 0 = 1) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ u : ℂ, ‖u‖ < ρ → ‖star (G u) - star u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨G₂, hG₂an, hG₂⟩ := hG.exists_eq_sum_add_pow_mul 2
  have hexp : ∀ u : ℂ, G u = u + u ^ 2 * G₂ u := by
    intro u
    rw [hG₂ u]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedDeriv_zero, iteratedDeriv_one, hG0, hG1]
    ring
  have hcont : ContinuousAt G₂ 0 := hG₂an.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ρ, hρ, hρb⟩ := hcont 1 (by norm_num)
  refine ⟨‖G₂ 0‖ + 1, ρ, hρ, fun u hu => ?_⟩
  have hb : ‖G₂ u‖ ≤ ‖G₂ 0‖ + 1 := by
    have h1 : dist (G₂ u) (G₂ 0) < 1 :=
      hρb (show dist u 0 < ρ from by simpa [dist_eq_norm] using hu)
    rw [dist_eq_norm] at h1
    have h2 : ‖G₂ u‖ ≤ ‖G₂ u - G₂ 0‖ + ‖G₂ 0‖ := by
      calc ‖G₂ u‖ = ‖(G₂ u - G₂ 0) + G₂ 0‖ := by ring_nf
        _ ≤ ‖G₂ u - G₂ 0‖ + ‖G₂ 0‖ := norm_add_le _ _
    linarith
  have hkey : star (G u) - star u = star u ^ 2 * star (G₂ u) := by
    simp only [hexp u, star_add, star_mul, star_pow, star_star]
    ring
  rw [hkey, norm_mul, norm_pow, norm_star, norm_star]
  calc ‖u‖ ^ 2 * ‖G₂ u‖ ≤ ‖u‖ ^ 2 * (‖G₂ 0‖ + 1) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (‖G₂ 0‖ + 1) * ‖u‖ ^ 2 := by ring

end

end Work.FatouCoord.Flower
