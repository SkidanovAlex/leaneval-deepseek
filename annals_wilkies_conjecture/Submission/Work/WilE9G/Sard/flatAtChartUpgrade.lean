import Mathlib
import Submission.Work.WilE9G.Sard.morseDefs
import Submission.Work.WilE9G.Sard.chartDiffBound

/-!
# The flatness upgrade along a chart

This file proves `Work.WilE9G.Sard.flatAtChartUpgrade`, one of the steps of the Morse
decomposition (`Work.WilE9G.Sard.morseDecomposition`): if the derivative of `F` along the chart
`γ` is flat of order `m - 1` at `x`, and `F (γ x) = 0`, then `F ∘ γ` is flat of order `m` at `x`.

The work is delegated to `Work.WilE9G.Sard.FlatAt.comp_of_fderiv` (Morse's Lemma 3.2), which
needs, on a ball around `x`:

* a uniform bound `‖fderiv ℝ γ z‖ ≤ L` (so that `γ` behaves like a Lipschitz map),
* differentiability of `γ` and of `F` along `γ`.

The first two come from `Work.WilE9G.Sard.chartDiffBound` (the chart is `C¹`, hence locally
Lipschitz with bounded derivative, near an interior point of its domain); differentiability of `F`
along `γ` comes from `U` being open and `γ` continuous.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.WilE9G.Sard

theorem flatAtChartUpgrade {d m : ℕ} (hm : 1 ≤ m)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : (Fin d → ℝ) → G} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (C : Work.WilE9G.Sard.ChartDatum d)
    {x : Fin C.t → ℝ}
    (hxC : x ∈ Metric.ball C.base C.rad) (hUx : C.γ x ∈ U)
    (h0 : F (C.γ x) = 0)
    (hflat : Work.WilE9G.Sard.FlatAt (fun z => fderiv ℝ F (C.γ z)) (m - 1) x) :
    Work.WilE9G.Sard.FlatAt (fun z => F (C.γ z)) m x := by
  -- The chart is differentiable near `x`, with a uniform bound on its derivative.
  obtain ⟨L, ρ₁, hLnn, hρ₁pos, hdiffγ₁, hbd₁⟩ :=
    chartDiffBound (γ := C.γ) (base := C.base) (rad := C.rad) (u := x)
      C.contdiffOn C.rad_pos hxC
  -- Hence it is continuous at `x`, and (as `U` is open and contains `γ x`) it maps a ball
  -- around `x` into `U`.
  have hcontx : ContinuousAt C.γ x :=
    (hdiffγ₁ x (by simpa using hρ₁pos.le)).continuousAt
  obtain ⟨δ, hδpos, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (hcontx.preimage_mem_nhds (hU.mem_nhds hUx))
  -- A radius satisfying all the bounds simultaneously.
  set ρ : ℝ := min (ρ₁ / 2) (δ / 2) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (by linarith) (by linarith)
  have hρρ₁ : ρ ≤ ρ₁ := by
    rw [hρdef]
    exact (min_le_left _ _).trans (by linarith)
  have hρδ : ρ ≤ δ / 2 := by rw [hρdef]; exact min_le_right _ _
  refine FlatAt.comp_of_fderiv (L := L) (ρ₀ := ρ) hm ?_ ?_ h0 hLnn hρpos ?_ hflat
  · -- `F` is differentiable at `γ z`, since `γ z ∈ U` and `U` is open
    intro z hz
    have hzδ : dist z x < δ := by rw [dist_eq_norm]; linarith
    have hzU : C.γ z ∈ U := hδsub (Metric.mem_ball.mpr hzδ)
    exact (hF.contDiffAt (hU.mem_nhds hzU)).differentiableAt_one
  · -- `γ` is differentiable at `z`
    intro z hz
    exact hdiffγ₁ z (le_trans hz hρρ₁)
  · -- the derivative of `γ` is bounded at `z`
    intro z hz
    exact hbd₁ z (le_trans hz hρρ₁)

end Work.WilE9G.Sard
