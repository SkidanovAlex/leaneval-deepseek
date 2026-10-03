import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Potential.removable_singularity_bounded_harmonic

namespace Work.SimplyConnected.ABS

open scoped Manifold ContDiff Topology
open Filter Set

/-- The local expansion of a function with a logarithmic pole.

If `E` is harmonic on `U \ {x₀}` and has a logarithmic pole at `x₀` in the preferred chart at
`x₀`, then in that chart the function `E + log ‖ζ - ζ x₀‖` is bounded near `ζ x₀` and harmonic off
`ζ x₀`; by the removable singularity theorem it extends to a harmonic function `H` on a disc around
`ζ x₀`, and `E x = -log ‖ζ x - ζ x₀‖ + H (ζ x)` there. -/
theorem localPoleExpansion_of_hasLogPoleOn {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {x₀ : X} (hU : U ∈ nhds x₀) {E : X → ℝ}
    (hharm : Submission.HarmonicOnX E (U \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn U x₀ E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ x₀) x₀) ρ) ∧
      (∀ x : X, x ∈ U → x ∈ Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ → x ≠ x₀ →
        E x = -Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ + H ((chartAt ℂ x₀) x)) := by
  obtain ⟨C, V, hVmem, hVbound⟩ := hpole
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have htgt : a ∈ c.target := by rw [ha]; exact c.map_source hsrc
  -- a disc around `a = c x₀` inside the chart target and inside the preimage of `V ∩ U`
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds htgt)
  have hcont : ContinuousAt c.symm a := c.continuousAt_symm htgt
  have hsa : c.symm a = x₀ := by rw [ha]; exact c.left_inv hsrc
  have hmem : c.symm ⁻¹' (V ∩ U) ∈ 𝓝 a :=
    hcont.preimage_mem_nhds (inter_mem (hsa ▸ hVmem) (hsa ▸ hU))
  obtain ⟨R₂, hR₂, hR₂sub⟩ := Metric.mem_nhds_iff.mp hmem
  set R : ℝ := min R₁ R₂ with hRdef
  have hR : 0 < R := by rw [hRdef]; exact lt_min hR₁ hR₂
  have hRt : Metric.ball a R ⊆ c.target :=
    (Metric.ball_subset_ball (by rw [hRdef]; exact min_le_left R₁ R₂)).trans hR₁sub
  have hRs : Metric.ball a R ⊆ c.symm ⁻¹' (V ∩ U) :=
    (Metric.ball_subset_ball (by rw [hRdef]; exact min_le_right R₁ R₂)).trans hR₂sub
  -- the function read in the chart, with the log term made explicit
  set u : ℂ → ℝ := fun z => E (c.symm z) + Real.log ‖z - a‖ with hu
  have hball_of : ∀ {z : ℂ} {ρ : ℝ}, ‖z - a‖ < ρ → z ∈ Metric.ball a ρ :=
    fun hz => Metric.mem_ball.mpr (by rwa [dist_eq_norm])
  have hharmu : ∀ z : ℂ, ‖z - a‖ < R → z ≠ a → InnerProductSpace.HarmonicAt u z := by
    intro z hz hzne
    have hztgt : z ∈ c.target := hRt (hball_of hz)
    have hzsrc : c.symm z ∈ c.source := c.map_target hztgt
    have hcy : c (c.symm z) = z := c.right_inv hztgt
    have hzne' : c.symm z ≠ x₀ := by
      intro h
      exact hzne (by rw [ha, ← hcy, h])
    have hzVU : c.symm z ∈ V ∩ U := hRs (hball_of hz)
    have hEX : Submission.HarmonicOnXAt E (c.symm z) :=
      hharm _ ⟨hzVU.2, by simpa using hzne'⟩
    have h1 : InnerProductSpace.HarmonicAt (E ∘ c.symm) z := by
      have h := (Submission.HarmonicOnXAt_iff_chart (u := E) (x := c.symm z) (y := x₀)
        hzsrc).mp hEX
      rwa [hcy] at h
    have h2 : InnerProductSpace.HarmonicAt (fun z : ℂ => Real.log ‖z - a‖) z := by
      have hne : z - a ≠ 0 := sub_ne_zero.mpr hzne
      exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
        (u := fun w : ℂ => Real.log ‖w‖) (f := fun z : ℂ => z - a) (x := z)
        (analyticAt_id.sub analyticAt_const)
        (AnalyticAt.harmonicAt_log_norm analyticAt_id hne)
    rw [hu]
    exact h1.add h2
  have hbu : ∀ z : ℂ, ‖z - a‖ < R → z ≠ a → |u z| ≤ C := by
    intro z hz hzne
    have hztgt : z ∈ c.target := hRt (hball_of hz)
    have hcy : c (c.symm z) = z := c.right_inv hztgt
    have hzne' : c.symm z ≠ x₀ := by
      intro h
      exact hzne (by rw [ha, ← hcy, h])
    have hzVU : c.symm z ∈ V ∩ U := hRs (hball_of hz)
    have h := hVbound (c.symm z) hzVU.1 hzVU.2 hzne'
    have h' : |E (c.symm z) + Real.log ‖z - a‖| ≤ C := by rwa [hcy] at h
    simpa only [hu] using h'
  obtain ⟨H, hHharm, hHeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := u) (a := a) (R := R) (M := C) hR hharmu hbu
  refine ⟨R / 2, by linarith, H, ?_, ?_⟩
  · intro z hz
    exact hHharm z (by
      have : dist z a < R / 2 := by rwa [Metric.mem_ball] at hz
      rwa [dist_eq_norm] at this)
  · intro x hxU hxb hxne
    obtain ⟨hxsrc, hxz⟩ := Submission.mem_chartBall.mp hxb
    have hcx_ne : c x ≠ a := by
      intro h
      exact hxne (c.injOn hxsrc hsrc h)
    have hH := hHeq (c x) (by
      have : dist (c x) a < R / 2 := by rwa [Metric.mem_ball] at hxz
      rwa [dist_eq_norm] at this) hcx_ne
    have hcu : u (c x) = E x + Real.log ‖c x - a‖ := by
      rw [hu]
      simp only [c.left_inv hxsrc]
    linarith [hH, hcu]

end Work.SimplyConnected.ABS
