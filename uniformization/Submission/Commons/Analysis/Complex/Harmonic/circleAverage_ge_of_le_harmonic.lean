import Mathlib
import Submission.Commons.Analysis.Complex.Dirichlet.dirichlet_ball

noncomputable section
open Set Metric Complex InnerProductSpace Filter
open scoped Real Topology

namespace Commons.Analysis.Complex.Harmonic

/-- **(Comparison criterion ⇒ mean-value inequality)**, the converse half of the
equivalence between the circle mean-value definition of subharmonicity and the comparison
principle. Let `Ω ⊆ ℂ` be open, `v` continuous on `Ω`, and suppose that for every closed
ball `Metric.closedBall p r ⊆ Ω` and every `h` harmonic on `Metric.ball p r` and continuous
on `Metric.closedBall p r` with `v ≤ h` on `Metric.sphere p r`, one has `v ≤ h` on
`Metric.ball p r`. Then `v` satisfies the circle mean-value inequality at every point of
`Ω`, i.e. `v p ≤ Real.circleAverage v p r` for every circle inside `Ω`.

Proof: let `h` be the Dirichlet solution on `Metric.ball p r` with boundary data `v`
(exists by commons `dirichlet_ball`); the criterion gives `v ≤ h` on the ball, so
`v p ≤ h p`; for every `ρ < r` the mean value property of the harmonic function `h` gives
`h p = Real.circleAverage h p ρ`, and `v ≤ h` yields
`Real.circleAverage v p ρ ≤ Real.circleAverage h p ρ`; letting `ρ → r` and using continuity
of circle averages in the radius, together with `h = v` on the sphere, gives
`v p ≤ Real.circleAverage v p r`. -/
theorem circleAverage_ge_of_le_harmonic {Ω : Set ℂ} (hΩopen : IsOpen Ω) {v : ℂ → ℝ}
    (hcont : ContinuousOn v Ω)
    (hcmp : ∀ (p : ℂ) (r : ℝ), 0 < r → Metric.closedBall p r ⊆ Ω → ∀ h : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd h (Metric.ball p r) → ContinuousOn h (Metric.closedBall p r) →
      (∀ z ∈ Metric.sphere p r, v z ≤ h z) → ∀ z ∈ Metric.ball p r, v z ≤ h z)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall p r ⊆ Ω) :
    v p ≤ Real.circleAverage v p r := by
  -- `v` is continuous on the boundary sphere, which lies in `Ω`.
  have hsphere_sub : Metric.sphere p r ⊆ Ω :=
    fun z hz => hball (sphere_subset_closedBall hz)
  have hsphere_cont : ContinuousOn v (Metric.sphere p r) := hcont.mono hsphere_sub
  -- Dirichlet solution on `ball p r` with boundary data `v`.
  obtain ⟨u, hu_harm, hu_cont⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := p) (R := r) hr hsphere_cont
  -- The function glued from `u` inside and `v` on the boundary.
  let h : ℂ → ℝ := fun z => if ‖z - p‖ < r then u z else v z
  have hu_cont' : ContinuousOn h (Metric.closedBall p r) := by
    simpa [h] using hu_cont
  have hHarm : InnerProductSpace.HarmonicOnNhd h (Metric.ball p r) := by
    intro z hz
    have hz_norm : ‖z - p‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have huz : InnerProductSpace.HarmonicAt u z := hu_harm z hz_norm
    have heq : h =ᶠ[𝓝 z] u := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      have hw_norm : ‖w - p‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      simp [h, hw_norm]
    exact (harmonicAt_congr_nhds heq).mpr huz
  -- `v ≤ h` on the boundary sphere.
  have hle_sphere : ∀ z ∈ Metric.sphere p r, v z ≤ h z := by
    intro z hz
    have hz_norm : ‖z - p‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hlt : ¬ ‖z - p‖ < r := by rw [hz_norm]; exact lt_irrefl r
    simp [h, hlt]
  -- The comparison criterion gives `v ≤ h` on the ball.
  have hle_ball : ∀ z ∈ Metric.ball p r, v z ≤ h z :=
    hcmp p r hr hball h hHarm hu_cont' hle_sphere
  have hp_ball : p ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_self]
    exact hr
  have hvp : v p ≤ h p := hle_ball p hp_ball
  -- Mean value property of the harmonic function `h`.
  have hMV : Real.circleAverage h p r = h p := by
    have hHCOC : HarmonicContOnCl h (Metric.ball p |r|) := by
      refine ⟨?_, ?_⟩
      · rw [abs_of_pos hr]
        exact hHarm
      · rw [abs_of_pos hr, closure_ball p hr.ne']
        exact hu_cont'
    exact InnerProductSpace.HarmonicContOnCl.circleAverage_eq hHCOC
  -- `h` and `v` agree on the circle, so their circle averages agree.
  have hcongr : Real.circleAverage h p r = Real.circleAverage v p r := by
    apply Real.circleAverage_congr_sphere
    rw [abs_of_pos hr]
    intro z hz
    have hz_norm : ‖z - p‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hlt : ¬ ‖z - p‖ < r := by rw [hz_norm]; exact lt_irrefl r
    simp [h, hlt]
  calc
    v p ≤ h p := hvp
    _ = Real.circleAverage h p r := hMV.symm
    _ = Real.circleAverage v p r := hcongr

end Commons.Analysis.Complex.Harmonic
