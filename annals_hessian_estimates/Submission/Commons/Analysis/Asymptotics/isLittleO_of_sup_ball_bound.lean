import Mathlib

namespace Commons.Analysis.Asymptotics

open MeasureTheory Metric Set Filter Function in
open scoped Topology in
theorem isLittleO_of_sup_ball_bound {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : h x = 0)
    (hsup : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ y ∈ Metric.ball x r, |h y| ≤ ε * r ^ 2) :
    h =o[𝓝 x] fun y => ‖y - x‖ ^ 2 := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hc4 : (0:ℝ) < c/4 := by linarith
  -- Extract a definite small radius δ from the hypothesis at level c/4.
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ r, 0 < r → r < δ →
      ∀ y ∈ Metric.ball x r, |h y| ≤ c/4 * r^2 := by
    have hq := hsup (c/4) hc4
    rw [eventually_nhdsWithin_iff] at hq
    rw [Metric.eventually_nhds_iff] at hq
    obtain ⟨δ, hδpos, hδ⟩ := hq
    exact ⟨δ, hδpos, fun r hr hrd y hy => hδ (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrd) (mem_Ioi.mpr hr) y hy⟩
  rw [eventually_iff]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x (show (0:ℝ) < δ/2 by linarith)) ?_
  intro y hy
  change ‖h y‖ ≤ c * ‖‖y - x‖ ^ 2‖
  by_cases hyx : y = x
  · rw [hyx]
    simp [hx]
  · have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    have hdlt : ‖y - x‖ < δ/2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy
    set r : ℝ := 2 * ‖y - x‖ with hr_def
    have hrpos : 0 < r := by rw [hr_def]; linarith
    have hrlt : r < δ := by rw [hr_def]; linarith
    have hymem : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, hr_def]; linarith
    have hbound : |h y| ≤ c/4 * r^2 := hδ r hrpos hrlt y hymem
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg _)]
    calc |h y| ≤ c/4 * r^2 := hbound
      _ = c * ‖y - x‖^2 := by rw [hr_def]; ring

end Commons.Analysis.Asymptotics
