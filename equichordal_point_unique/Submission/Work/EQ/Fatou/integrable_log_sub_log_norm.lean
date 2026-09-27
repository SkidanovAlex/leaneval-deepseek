import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory

/-- For `h` holomorphic on the unit disc and `0 < ρ < 1`, the function
`θ ↦ log B - log ‖h (ρ e^{iθ})‖` is integrable on `(0, 2π]`.

This is a special case of the integrability of `log ‖f‖` for meromorphic `f`
(`MeromorphicOn.circleIntegrable_log_norm`): a function differentiable on the open unit ball is
analytic there, hence meromorphic on the circle of radius `ρ`, and `CircleIntegrable` unfolds
to interval integrability of the parametrised function. -/
theorem integrable_log_sub_log_norm {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    {ρ B : ℝ} (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    MeasureTheory.Integrable
      (fun θ : ℝ => Real.log B - Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖)
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
  have hρpos : 0 < ρ := hρ.1
  have hρlt : ρ < 1 := hρ.2
  -- `h` is analytic, hence meromorphic, on the circle of radius `ρ`
  have hmer : MeromorphicOn h (Metric.sphere 0 |ρ|) := by
    rw [abs_of_pos hρpos]
    intro z hz
    have hznorm : ‖z‖ = ρ := by
      rw [← dist_zero_right]
      simpa [Metric.mem_sphere] using hz
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hznorm]
      exact hρlt
    exact (hh.analyticAt (Metric.isOpen_ball.mem_nhds hz1)).meromorphicAt
  -- circle integrability of `log ‖h ·‖`
  have hci : CircleIntegrable (fun z => Real.log ‖h z‖) 0 ρ :=
    MeromorphicOn.circleIntegrable_log_norm hmer
  -- unfold `CircleIntegrable` into an interval integral
  have hii : IntervalIntegrable
      (fun θ : ℝ => Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖)
      volume 0 (2 * Real.pi) := by
    rw [circleIntegrable_def] at hci
    simpa only [circleMap_zero] using hci
  -- convert to integrability on the restricted measure
  have hInt : MeasureTheory.Integrable
      (fun θ : ℝ => Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖)
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hii
  -- subtract the constant `log B`
  exact (integrable_const (Real.log B)).sub hInt

end Work.EQ.Fatou
