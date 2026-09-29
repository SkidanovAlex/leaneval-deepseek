import Mathlib

namespace Work.Holonomy3

open Complex Filter Metric Real Set Topology
open scoped Real Interval

/-- If `g` is continuous on the closed unit disk and nowhere zero on the unit circle, then
`g` is bounded away from zero on a closed annulus `a ≤ ‖z‖ ≤ 1` with `0 < a < 1`. -/
theorem exists_annulus_ne_zero (g : ℂ → ℂ) (hg : ContinuousOn g (Metric.closedBall 0 1))
    (hne : ∀ z : ℂ, ‖z‖ = 1 → g z ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ 1 → g z ≠ 0 := by
  have hKclosed : IsClosed (Metric.closedBall 0 1 ∩ g ⁻¹' {0}) :=
    hg.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton
  have hKcompact : IsCompact (Metric.closedBall 0 1 ∩ g ⁻¹' {0}) :=
    (ProperSpace.isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hKclosed Set.inter_subset_left
  by_cases hK : (Metric.closedBall 0 1 ∩ g ⁻¹' {0}).Nonempty
  · obtain ⟨z1, hz1K, hz1max⟩ := hKcompact.exists_isMaxOn hK continuous_norm.continuousOn
    have hz1mem : z1 ∈ Metric.closedBall 0 1 := hz1K.1
    have hz1g : g z1 = 0 := hz1K.2
    have hz1le : ‖z1‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz1mem
    have hz1lt : ‖z1‖ < 1 := by
      rcases lt_or_eq_of_le hz1le with h | h
      · exact h
      · exact absurd (hne z1 h) (by simp [hz1g])
    refine ⟨(‖z1‖ + 1) / 2, by linarith [norm_nonneg z1], by linarith, ?_⟩
    intro z hz hz' hgz
    have hzemem : z ∈ Metric.closedBall 0 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz'
    have hzg : z ∈ g ⁻¹' {0} := by simpa using hgz
    have hle : ‖z‖ ≤ ‖z1‖ := hz1max ⟨hzemem, hzg⟩
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro z _ hz' hgz
    apply hK
    refine ⟨z, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right] using hz'
    · simpa using hgz

theorem circleAverage_log_norm_tendsto (g : ℂ → ℂ) (hg : ContinuousOn g (Metric.closedBall 0 1))
    (hne : ∀ z : ℂ, ‖z‖ = 1 → g z ≠ 0) :
    Filter.Tendsto (fun r : ℝ => Real.circleAverage (fun z => Real.log ‖g z‖) 0 r)
      (nhdsWithin (1:ℝ) (Set.Iio 1))
      (nhds (Real.circleAverage (fun z => Real.log ‖g z‖) 0 1)) := by
  obtain ⟨a, ha0, ha1, ha⟩ := exists_annulus_ne_zero g hg hne
  have hf : ContinuousOn (fun z : ℂ => Real.log ‖g z‖) {z : ℂ | ‖z - 0‖ ∈ Set.Icc a 1} := by
    apply ContinuousOn.log
    · apply ContinuousOn.norm
      apply hg.mono
      intro z hz
      simp only [sub_zero, Set.mem_Icc] at hz
      simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
    · intro z hz
      simp only [sub_zero, Set.mem_Icc] at hz
      exact norm_ne_zero_iff.mpr (ha z hz.1 hz.2)
  have hcont : ContinuousOn
      (fun r : ℝ => Real.circleAverage (fun z => Real.log ‖g z‖) 0 r) (Set.Icc a 1) :=
    ContinuousOn.circleAverage (f := fun z => Real.log ‖g z‖) (c := 0) (s := Set.Icc a 1) hf
      (fun r hr => le_trans (le_of_lt ha0) hr.1)
  have h1 : (1:ℝ) ∈ Set.Icc a 1 := ⟨le_of_lt ha1, le_refl 1⟩
  have hle : nhdsWithin (1:ℝ) (Set.Iio 1) ≤ nhdsWithin (1:ℝ) (Set.Icc a 1) := by
    rw [nhdsWithin_le_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1 - a, by linarith, ?_⟩
    intro x hx
    obtain ⟨hxball, hxio⟩ := hx
    rw [Metric.mem_ball, Real.dist_eq] at hxball
    rw [abs_lt] at hxball
    exact ⟨le_of_lt (by linarith [hxball.1]), le_of_lt hxio⟩
  exact (hcont 1 h1).mono_left hle

end Work.Holonomy3
