import Mathlib
import Submission.Work.EQ.Fatou.log_norm_le_integral

/-!
# Jensen bound for the integral of `log B - log ‖h‖` over a circle

For a holomorphic `h` on the unit disc with `h 0 ≠ 0`, a radius `ρ ∈ (0,1)` and any `B : ℝ`, the
average of `log ‖h‖` on the circle of radius `ρ` dominates `log ‖h 0‖` (Jensen's inequality,
`LogNormLeIntegral`), hence the integral of `log B - log ‖h‖` is bounded by
`2π log B - 2π log ‖h 0‖`.

The only analytic input is `Work.EQ.Fatou.log_norm_le_integral`.  The remaining work is to
(i) recognise the interval integral as an integral against `volume.restrict (Ioc 0 (2π))`,
(ii) show that `θ ↦ log ‖h (ρ exp (θ i))‖` is integrable there (circle integrability of the log
modulus of a meromorphic function), and (iii) split the integral and evaluate the constant part.
-/

namespace Work.EQ.Fatou

open MeasureTheory

theorem integral_log_sub_log_norm_le {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) (h0 : h 0 ≠ 0)
    {ρ B : ℝ} (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    ∫ θ, (Real.log B - Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖)
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      ≤ 2 * Real.pi * Real.log B - 2 * Real.pi * Real.log ‖h 0‖ := by
  obtain ⟨hρpos, hρlt⟩ := hρ
  -- basic positivity facts about `2π`
  have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have h2pine : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  -- `h` is analytic on the closed ball of radius `ρ < 1`
  have h_an : AnalyticOnNhd ℂ h (Metric.closedBall 0 ρ) := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    exact hh.analyticAt (Metric.isOpen_ball.mem_nhds
      (by rw [Metric.mem_ball]; simpa using lt_of_le_of_lt hx hρlt))
  -- integrability of the logarithmic term on the circle of radius `ρ`
  have hInt_g : MeasureTheory.Integrable
      (fun θ : ℝ => Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖)
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    have hci : CircleIntegrable (fun z => Real.log ‖h z‖) 0 ρ :=
      (h_an.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg
        (le_of_lt hρpos)
    have h1 := hci.1
    simpa only [MeasureTheory.IntegrableOn, circleMap, zero_add] using h1
  -- integrability of the constant term
  have hInt_c : MeasureTheory.Integrable (fun _ : ℝ => Real.log B)
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) := MeasureTheory.integrable_const _
  -- split the integral into its two parts
  rw [MeasureTheory.integral_sub hInt_c hInt_g]
  -- the total mass of the restricted measure is `2π`
  have hvol : (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))).real Set.univ
      = 2 * Real.pi := by
    simp only [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Ioc, sub_zero]
    rw [ENNReal.toReal_ofReal h2pi]
  have hconst : ∫ _ : ℝ, Real.log B
      ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))) = 2 * Real.pi * Real.log B := by
    rw [MeasureTheory.integral_const, hvol, smul_eq_mul]
  rw [hconst]
  -- it remains to bound the logarithmic integral below by `2π log ‖h 0‖`
  apply sub_le_sub_left
  have hJ := log_norm_le_integral h hρpos hρlt hh h0
  have hJ' : Real.log ‖h 0‖ ≤ (2 * Real.pi)⁻¹ *
      (∫ θ, Real.log ‖h (ρ * Complex.exp ((θ:ℂ) * Complex.I))‖
        ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    rw [intervalIntegral.integral_of_le h2pi] at hJ
    simpa using hJ
  have hthis := mul_le_mul_of_nonneg_left hJ' h2pi
  rwa [← mul_assoc, mul_inv_cancel₀ h2pine, one_mul] at hthis

end Work.EQ.Fatou
