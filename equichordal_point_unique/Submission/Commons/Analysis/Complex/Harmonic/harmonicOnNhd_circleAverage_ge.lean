import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Harmonic.MeanValue

namespace Commons.Analysis.Complex.Harmonic

/-- A harmonic function satisfies the circle mean-value inequality (in particular it is
subharmonic): if `v` is harmonic on the open ball `Metric.ball a ρ` (`ρ > 0`) and
`‖p - a‖ + r < ρ` with `r > 0`, then `v p ≤ Real.circleAverage v p r`. Since `v` is harmonic
on a neighbourhood of the closed ball `Metric.closedBall p r ⊆ Metric.ball a ρ`, this is the
forward mean value property `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`. -/
theorem harmonicOnNhd_circleAverage_ge {v : ℂ → ℝ} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hv : InnerProductSpace.HarmonicOnNhd v (Metric.ball a ρ)) {p : ℂ} (hp : ‖p - a‖ < ρ)
    {r : ℝ} (hr : 0 < r) (hpr : ‖p - a‖ + r < ρ) :
    v p ≤ Real.circleAverage v p r := by
  have hsub : Metric.closedBall p r ⊆ Metric.ball a ρ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖x - a‖ = ‖(x - p) + (p - a)‖ := by ring_nf
      _ ≤ ‖x - p‖ + ‖p - a‖ := norm_add_le _ _
      _ < ρ := by linarith
  have hnhd : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall p |r|) := by
    rw [abs_of_pos hr]
    exact hv.mono hsub
  exact le_of_eq (InnerProductSpace.HarmonicOnNhd.circleAverage_eq hnhd).symm

end Commons.Analysis.Complex.Harmonic