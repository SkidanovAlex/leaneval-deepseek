import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.localPoleExpansion

/-!
# The pole bound of the Green function in the preferred chart

Let `X` be a connected complex one-manifold (a Riemann surface), `z₀ : X`, and let `E : X → ℝ` be a
Green function at `z₀` in the sense of `Work.UnitGreen.IsUnitGreenFunctionAt`: positive and harmonic
off `z₀`, with a logarithmic pole of coefficient one at `z₀`, and decaying to `0` at the ideal
boundary.

This module extracts the *boundedness* content of the logarithmic pole.  By
`Work.Modulus.localPoleExpansion`, in the preferred chart `c = chartAt ℂ z₀` the Green function has
the form
`E x = -log ‖c x - c z₀‖ + H (c x)`
with `H` harmonic on a disc `Metric.ball (c z₀) ρ`.  A harmonic function is continuous on that disc,
and hence bounded on any strictly smaller closed disc.  Shrinking further so that the disc stays
inside `c.target`, we obtain a radius `ε > 0` on which

`|E (c.symm w) + log ‖w - c z₀‖| ≤ C`

for every `w ≠ c z₀` in the disc — i.e. the corrected function `w ↦ E (c.symm w) + log ‖w - c z₀‖`
is bounded near the pole, and `c.symm w ≠ z₀` for `w ≠ c z₀`.

This is the quantitative form of the pole that the *lower* bounds on the modulus of a holomorphic
function with a simple zero consume (cf. `Work.Modulus.simpleZeroOfGrowth`).
-/

open scoped Topology

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

theorem chartPoleBound
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball ((chartAt ℂ z₀) z₀) ε ⊆ (chartAt ℂ z₀).target ∧
      ∃ C : ℝ, ∀ w ∈ Metric.ball ((chartAt ℂ z₀) z₀) ε, w ≠ (chartAt ℂ z₀) z₀ →
        (chartAt ℂ z₀).symm w ≠ z₀ ∧
        |E ((chartAt ℂ z₀).symm w) + Real.log ‖w - (chartAt ℂ z₀) z₀‖| ≤ C := by
  -- the local expansion of `E` at its pole, in the preferred chart
  obtain ⟨ρ, hρ, H, hH, hexp⟩ := localPoleExpansion hE
  set a : ℂ := (chartAt ℂ z₀) z₀ with ha
  have hatgt : a ∈ (chartAt ℂ z₀).target := by
    rw [ha]
    exact (chartAt ℂ z₀).map_source (mem_chart_source ℂ z₀)
  -- a disc around `a` contained in the chart target
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ((chartAt ℂ z₀).open_target.mem_nhds hatgt)
  -- the radius we will use: half of both radii, so that the closed disc stays inside both
  set r : ℝ := min (ρ / 2) (δ / 2) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- `H` is continuous on the closed disc of radius `r`, hence bounded there
  have hbdd : ∃ C : ℝ, ∀ w ∈ Metric.closedBall a r, |H w| ≤ C := by
    have hcont : ContinuousOn H (Metric.closedBall a r) :=
      hH.continuousOn.mono (Metric.closedBall_subset_ball hrρ)
    obtain ⟨C, hC⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hcont
    exact ⟨C, fun w hw => by rw [← Real.norm_eq_abs]; exact hC w hw⟩
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨r, hrpos, ?_, C, ?_⟩
  · exact (Metric.ball_subset_ball hrδ.le).trans hδsub
  · intro w hw hwne
    have hwt : w ∈ (chartAt ℂ z₀).target := hδsub (Metric.ball_subset_ball hrδ.le hw)
    have hcs : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm w) = w := (chartAt ℂ z₀).right_inv hwt
    have hsne : (chartAt ℂ z₀).symm w ≠ z₀ := by
      intro hcon
      exact hwne (by rw [← hcs, hcon, ha])
    refine ⟨hsne, ?_⟩
    -- the expansion applies at `c.symm w`
    have hmem : (chartAt ℂ z₀).symm w ∈ Submission.chartBall (chartAt ℂ z₀) a ρ := by
      refine ⟨OpenPartialHomeomorph.map_target _ hwt, ?_⟩
      change (chartAt ℂ z₀) ((chartAt ℂ z₀).symm w) ∈ Metric.ball a ρ
      rw [hcs]
      exact Metric.ball_subset_ball hrρ.le hw
    have hval := hexp ((chartAt ℂ z₀).symm w) hmem hsne
    rw [hval, hcs]
    have harith : -(Real.log ‖w - a‖) + H w + Real.log ‖w - a‖ = H w := by ring
    rw [harith]
    exact hC w (Metric.ball_subset_closedBall hw)

end Work.Modulus
