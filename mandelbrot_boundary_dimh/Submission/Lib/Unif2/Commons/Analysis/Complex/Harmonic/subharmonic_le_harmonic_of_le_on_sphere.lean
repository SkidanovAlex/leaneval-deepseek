import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.max_principle_subharmonic

namespace Commons.Analysis.Complex.Harmonic

/-- **(Mean-value inequality ⇒ comparison criterion)**, the easy half of the equivalence
between the circle mean-value definition of subharmonicity and the comparison principle.
Let `Ω ⊆ ℂ` be open and `v` continuous on `Ω` with the circle mean-value inequality
`v p ≤ Real.circleAverage v p r` at every point of `Ω` (for every circle inside `Ω`).
Then for every closed ball `Metric.closedBall p r ⊆ Ω` and every `h` harmonic on the open
ball `Metric.ball p r` and continuous on `Metric.closedBall p r`, if `v ≤ h` on the sphere
`Metric.sphere p r` then `v ≤ h` on the whole ball. -/
theorem subharmonic_le_harmonic_of_le_on_sphere {Ω : Set ℂ} (hΩopen : IsOpen Ω) {v : ℂ → ℝ}
    (hcont : ContinuousOn v Ω)
    (hMVP : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      v p ≤ Real.circleAverage v p r)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall p r ⊆ Ω) {h : ℂ → ℝ}
    (hharm : InnerProductSpace.HarmonicOnNhd h (Metric.ball p r))
    (hcont_h : ContinuousOn h (Metric.closedBall p r))
    (hle : ∀ z ∈ Metric.sphere p r, v z ≤ h z) :
    ∀ z ∈ Metric.ball p r, v z ≤ h z := by
  have _ := hΩopen
  have hvb : ContinuousOn v (Metric.closedBall p r) := hcont.mono hball
  have hgcont : ContinuousOn (fun z : ℂ => v z - h z) (Metric.closedBall p r) :=
    hvb.sub hcont_h
  -- sub-mean-value inequality for `v - h` on the open ball
  have hgsub : ∀ q : ℂ, ‖q - p‖ < r → ∀ ρ : ℝ, 0 < ρ → ‖q - p‖ + ρ < r →
      v q - h q ≤ Real.circleAverage (fun z : ℂ => v z - h z) q ρ := by
    intro q hq ρ hρ hqρ
    have hq_cl : q ∈ Metric.closedBall p r := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have hsub_cl : Metric.closedBall q ρ ⊆ Metric.closedBall p r := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
      have h1 : ‖w - p‖ ≤ ‖w - q‖ + ‖q - p‖ := by
        simpa [dist_eq_norm] using dist_triangle w q p
      linarith
    have hsubΩ : Metric.closedBall q ρ ⊆ Ω := hsub_cl.trans hball
    have hqΩ : q ∈ Ω := hball hq_cl
    have hv := hMVP q hqΩ ρ hρ hsubΩ
    have hharm_cl : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall q |ρ|) := by
      refine hharm.mono ?_
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      rw [abs_of_pos hρ] at hw
      have h1 : ‖w - p‖ ≤ ‖w - q‖ + ‖q - p‖ := by
        simpa [dist_eq_norm] using dist_triangle w q p
      linarith
    have hhavg : Real.circleAverage h q ρ = h q :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm_cl
    have hcont_sph_v : ContinuousOn v (Metric.sphere q |ρ|) := by
      refine hcont.mono ?_
      intro x hx
      apply hsubΩ
      rw [Metric.mem_sphere, dist_eq_norm] at hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [abs_of_pos hρ] at hx
      exact le_of_eq hx
    have hcont_sph_h : ContinuousOn h (Metric.sphere q |ρ|) := by
      refine hcont_h.mono ?_
      intro x hx
      apply hsub_cl
      rw [Metric.mem_sphere, dist_eq_norm] at hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [abs_of_pos hρ] at hx
      exact le_of_eq hx
    have hint_v : CircleIntegrable v q ρ := hcont_sph_v.circleIntegrable'
    have hint_h : CircleIntegrable h q ρ := hcont_sph_h.circleIntegrable'
    have hsplit :
        Real.circleAverage (fun z : ℂ => v z - h z) q ρ
          = Real.circleAverage v q ρ - Real.circleAverage h q ρ :=
      Real.circleAverage_fun_sub hint_v hint_h
    rw [hsplit, hhavg]
    linarith
  -- boundary values of `v - h` are ≤ 0 on the sphere
  have hgbd : ∀ z : ℂ, ‖z - p‖ = r → (fun z : ℂ => v z - h z) z ≤ 0 := by
    intro z hz
    have hzsph : z ∈ Metric.sphere p r := by
      rw [Metric.mem_sphere, dist_eq_norm]; exact hz
    have h1 : v z - h z ≤ 0 := by
      have := hle z hzsph
      linarith
    exact h1
  have hmain := max_principle_subharmonic (g := fun z : ℂ => v z - h z) (c := p) (R := r)
    hr hgcont hgsub hgbd
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h2 : v z - h z ≤ 0 := hmain z (le_of_lt hz)
  linarith

end Commons.Analysis.Complex.Harmonic