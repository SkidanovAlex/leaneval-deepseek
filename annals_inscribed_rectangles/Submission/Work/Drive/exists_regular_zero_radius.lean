import Mathlib

namespace Work.Drive

open scoped Topology

/-- If a `C¹` function `h : ℝ² → ℝ` has no critical zeros in the closed unit disc, then the same
holds in a slightly larger closed disc: a critical zero at distance `≤ 1 + ε` for every `ε > 0`
would, by compactness of the closed disc of radius `2`, accumulate at a point `z` with `‖z‖ ≤ 1`,
which would then be a critical zero by continuity of `h` and of `fderiv ℝ h`. -/
theorem exists_regular_zero_radius (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hh : ContDiff ℝ 1 h)
    (hreg : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ ≤ 1 → fderiv ℝ h z ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ ≤ 1 + ε →
      fderiv ℝ h z ≠ 0 := by
  by_contra hc
  push Not at hc
  -- For every `ε > 0` there is a critical zero at distance `≤ 1 + ε`.
  have hz' : ∀ n : ℕ, ∃ z : EuclideanSpace ℝ (Fin 2),
      h z = 0 ∧ ‖z‖ ≤ 1 + 1 / ((n : ℝ) + 1) ∧ fderiv ℝ h z = 0 := by
    intro n
    exact hc (1 / ((n : ℝ) + 1)) (by positivity)
  choose a ha using hz'
  have hcont : Continuous h := hh.continuous
  have hdcont : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hle1 : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hmem : ∀ n : ℕ, a n ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := (ha n).2.1
    have h2 := hle1 n
    linarith
  obtain ⟨x, -, φ, hφ, hφtend⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2).tendsto_subseq hmem
  have hx0 : h x = 0 := by
    have ht : Filter.Tendsto (fun n => h (a (φ n))) Filter.atTop (𝓝 (h x)) :=
      (hcont.tendsto x).comp hφtend
    have h0 : (fun n => h (a (φ n))) = fun _ => (0 : ℝ) := by
      funext n; exact (ha (φ n)).1
    rw [h0] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  have hxd : fderiv ℝ h x = 0 := by
    have ht : Filter.Tendsto (fun n => fderiv ℝ h (a (φ n))) Filter.atTop
        (𝓝 (fderiv ℝ h x)) :=
      (hdcont.tendsto x).comp hφtend
    have h0 : (fun n => fderiv ℝ h (a (φ n))) =
        fun _ => (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) := by
      funext n; exact (ha (φ n)).2.2
    rw [h0] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  have hxn : ‖x‖ ≤ 1 := by
    have h1 : Filter.Tendsto (fun n => ‖a (φ n)‖) Filter.atTop (𝓝 ‖x‖) :=
      (continuous_norm.tendsto x).comp hφtend
    have h2 : Filter.Tendsto (fun n : ℕ => 1 + (1 : ℝ) / ((φ n : ℝ) + 1)) Filter.atTop (𝓝 1) := by
      have h3 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((φ n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      simpa using tendsto_const_nhds.add h3
    have h3 : ∀ n : ℕ, ‖a (φ n)‖ ≤ 1 + (1 : ℝ) / ((φ n : ℝ) + 1) :=
      fun n => (ha (φ n)).2.1
    exact le_of_tendsto_of_tendsto' h1 h2 h3
  exact (hreg x hx0 hxn) hxd

end Work.Drive
