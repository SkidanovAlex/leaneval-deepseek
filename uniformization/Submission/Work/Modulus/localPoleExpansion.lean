import Mathlib
import Submission.Work.Modulus.Defs
import Submission.Work.Potential.removable_singularity_bounded_harmonic

/-!
# The local expansion of the Green function at its pole

If `E` is a Green function at `z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt` — positive and
harmonic off `z₀`, with a logarithmic pole of coefficient one at `z₀` and decay at the ideal
boundary — then, in the preferred chart at `z₀`, `E` has the local form

`E x = -log ‖c x - c z₀‖ + H (c x)`,

where `H` is harmonic on some disc `Metric.ball (c z₀) ρ`, `ρ > 0`.

The proof is entirely local.  Reading `E` in the chart at `z₀` gives a function harmonic on the
punctured disc `{0 < ‖ξ - c z₀‖ < R}`, and the pole condition says exactly that the corrected
function `ξ ↦ E (c.symm ξ) + log ‖ξ - c z₀‖` is *bounded* there.  Bounded harmonic functions on a
punctured disc have a removable singularity (`Work.Potential.removable_singularity_ball_center`),
which produces `H`.
-/

open scoped Topology

noncomputable section

open Filter Set

namespace Work.Modulus

theorem localPoleExpansion
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ z₀) z₀) ρ) ∧
      (∀ x ∈ Submission.chartBall (chartAt ℂ z₀) ((chartAt ℂ z₀) z₀) ρ, x ≠ z₀ →
        E x = -Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ + H ((chartAt ℂ z₀) x)) := by
  -- unpack the strong Green-function data
  have hpos : ∀ x : X, x ≠ z₀ → 0 < E x := hE.1.1
  have hharm : Submission.HarmonicOnX E (univ \ {z₀}) := hE.1.2.1
  obtain ⟨C, V, hVnhds, hVbnd⟩ := hE.2
  have hsrc : z₀ ∈ (chartAt ℂ z₀).source := mem_chart_source ℂ z₀
  have hsymm₀ : (chartAt ℂ z₀).symm ((chartAt ℂ z₀) z₀) = z₀ := (chartAt ℂ z₀).left_inv hsrc
  have htgt₀ : (chartAt ℂ z₀) z₀ ∈ (chartAt ℂ z₀).target := (chartAt ℂ z₀).map_source hsrc
  -- a disc on which the pole bound holds, and which stays inside the chart target
  have hW : V ∩ (chartAt ℂ z₀).source ∈ 𝓝 z₀ :=
    inter_mem hVnhds ((chartAt ℂ z₀).open_source.mem_nhds hsrc)
  have hpre : (chartAt ℂ z₀).symm ⁻¹' (V ∩ (chartAt ℂ z₀).source) ∈ 𝓝 ((chartAt ℂ z₀) z₀) :=
    ContinuousAt.preimage_mem_nhds
      ((chartAt ℂ z₀).continuousAt_symm htgt₀) (by simpa [hsymm₀] using hW)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds htgt₀)
  set R : ℝ := min ε δ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hε hδ
  have hRε : Metric.ball ((chartAt ℂ z₀) z₀) R ⊆ (chartAt ℂ z₀).symm ⁻¹'
      (V ∩ (chartAt ℂ z₀).source) := by
    rw [hRdef]; exact (Metric.ball_subset_ball (min_le_left ε δ)).trans hεsub
  have hRδ : Metric.ball ((chartAt ℂ z₀) z₀) R ⊆ (chartAt ℂ z₀).target := by
    rw [hRdef]; exact (Metric.ball_subset_ball (min_le_right ε δ)).trans hδsub
  -- the corrected function is harmonic and bounded on the punctured disc, hence removable
  obtain ⟨H, hHharm, hHeq⟩ := Work.Potential.removable_singularity_ball_center
    (u := fun ξ : ℂ => E ((chartAt ℂ z₀).symm ξ) + Real.log ‖ξ - (chartAt ℂ z₀) z₀‖)
    (a := (chartAt ℂ z₀) z₀) (R := R) (M := C) hRpos
    (fun z hz hzne => by
      have hzR : z ∈ Metric.ball ((chartAt ℂ z₀) z₀) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hz
      have hzpre : (chartAt ℂ z₀).symm z ∈ V ∩ (chartAt ℂ z₀).source := hRε hzR
      have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
        (chartAt ℂ z₀).right_inv (hRδ hzR)
      have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := fun hcon => hzne (by rw [← hcs, hcon])
      have hEharm : InnerProductSpace.HarmonicAt (E ∘ (chartAt ℂ z₀).symm) z := by
        have h1 : Submission.HarmonicOnXAt E ((chartAt ℂ z₀).symm z) :=
          hharm _ ⟨mem_univ _, hyne⟩
        have h2 := (Submission.HarmonicOnXAt_iff_chart (u := E)
          (x := (chartAt ℂ z₀).symm z) (y := z₀) hzpre.2).mp h1
        rwa [hcs] at h2
      have hlogharm : InnerProductSpace.HarmonicAt
          (fun ξ : ℂ => Real.log ‖ξ - (chartAt ℂ z₀) z₀‖) z :=
        AnalyticAt.harmonicAt_log_norm (f := fun ξ : ℂ => ξ - (chartAt ℂ z₀) z₀)
          (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
      exact hEharm.add hlogharm)
    (fun z hz hzne => by
      have hzR : z ∈ Metric.ball ((chartAt ℂ z₀) z₀) R := by
        rw [Metric.mem_ball, dist_eq_norm]; exact hz
      have hzpre : (chartAt ℂ z₀).symm z ∈ V ∩ (chartAt ℂ z₀).source := hRε hzR
      have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm z) = z :=
        (chartAt ℂ z₀).right_inv (hRδ hzR)
      have hyne : (chartAt ℂ z₀).symm z ≠ z₀ := fun hcon => hzne (by rw [← hcs, hcon])
      have h1 := hVbnd ((chartAt ℂ z₀).symm z) hzpre.1 hyne
      rw [hcs] at h1
      exact h1)
  refine ⟨R / 2, by linarith, H, ?_, ?_⟩
  · intro z hz
    exact hHharm z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  · intro x hx hxne
    rw [Submission.mem_chartBall] at hx
    obtain ⟨hxsrc, hxball⟩ := hx
    have hcxne : (chartAt ℂ z₀) x ≠ (chartAt ℂ z₀) z₀ :=
      fun hcon => hxne ((chartAt ℂ z₀).injOn hxsrc hsrc hcon)
    have hlt : ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ < R / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    have hval := hHeq ((chartAt ℂ z₀) x) hlt hcxne
    rw [(chartAt ℂ z₀).left_inv hxsrc] at hval
    linarith

end Work.Modulus
