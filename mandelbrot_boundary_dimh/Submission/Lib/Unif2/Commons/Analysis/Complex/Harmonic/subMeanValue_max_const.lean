import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Harmonic.MeanValue

namespace Commons.Analysis.Complex.Harmonic

open Metric

theorem subMeanValue_max_const {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {u : ℂ → ℝ} {c : ℝ}
    (hu : ∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt u z) :
    ∀ z : ℂ, ‖z - a‖ < ρ → ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Metric.ball a ρ →
      max (u z) c ≤ Real.circleAverage (fun w : ℂ => max (u w) c) z r := by
  intro z _hr0 r hr hsub
  have _ : 0 < ρ := hρ
  -- `u` is harmonic on the open ball, hence on a neighbourhood of `closedBall z r`.
  have huOn : InnerProductSpace.HarmonicOnNhd u (Metric.ball a ρ) :=
    fun x hx => hu x (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
  have huBall : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall z |r|) := by
    rw [abs_of_pos hr]
    exact huOn.mono hsub
  -- Mean value property of `u`.
  have hmv : Real.circleAverage u z r = u z :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq huBall
  -- Continuity / integrability on the circle.
  have hcu : ContinuousOn u (Metric.sphere z r) :=
    (huOn.continuousOn.mono hsub).mono Metric.sphere_subset_closedBall
  have hcv : ContinuousOn (fun w : ℂ => max (u w) c) (Metric.sphere z r) :=
    hcu.sup continuousOn_const
  have hint_u : CircleIntegrable u z r := hcu.circleIntegrable hr.le
  have hint_v : CircleIntegrable (fun w : ℂ => max (u w) c) z r := hcv.circleIntegrable hr.le
  -- `u ≤ max u c` pointwise on the circle.
  have huv : Real.circleAverage u z r ≤ Real.circleAverage (fun w : ℂ => max (u w) c) z r :=
    Real.circleAverage_mono hint_u hint_v (fun x _ => le_max_left _ _)
  -- `c ≤ max u c` pointwise on the circle.
  have hcv' : c ≤ Real.circleAverage (fun w : ℂ => max (u w) c) z r := by
    have h := Real.circleAverage_mono (circleIntegrable_const c z r) hint_v
      (fun x _ => le_max_right (u x) c)
    rwa [Real.circleAverage_const c z r] at h
  exact max_le (hmv ▸ huv) hcv'

end Commons.Analysis.Complex.Harmonic