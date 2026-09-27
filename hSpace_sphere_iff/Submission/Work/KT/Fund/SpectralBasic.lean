import Mathlib
import Submission.Work.KT.Fund.SpectralAux

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The resolvent commutes with `b`. -/
theorem res_comm (b : A) {z : ℂ} (hz : IsUnit (z • 1 - b)) :
    Res b z * b = b * Res b z := by
  have h1 : Ring.inverse (z • 1 - b) * (z • 1 - b) = 1 := Ring.inverse_mul_cancel _ hz
  have h2 : b * (z • 1 - b) = (z • 1 - b) * b := by
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
  show Ring.inverse (z • 1 - b) * b = b * Ring.inverse (z • 1 - b)
  calc Ring.inverse (z • 1 - b) * b
      = Ring.inverse (z • 1 - b) * b * ((z • 1 - b) * Ring.inverse (z • 1 - b)) := by
        rw [Ring.mul_inverse_cancel _ hz, mul_one]
    _ = Ring.inverse (z • 1 - b) * (b * (z • 1 - b)) * Ring.inverse (z • 1 - b) := by
        noncomm_ring
    _ = Ring.inverse (z • 1 - b) * ((z • 1 - b) * b) * Ring.inverse (z • 1 - b) := by rw [h2]
    _ = b * Ring.inverse (z • 1 - b) := by
        rw [← mul_assoc, h1, one_mul]

/-- `b` commutes with the contour-integral projection. -/
theorem spectral_comm (b : A) {ρ : ℝ} (hρpos : 0 < ρ)
    (hcirc : ∀ z : ℂ, ‖z‖ = ρ → IsUnit (z • 1 - b)) :
    b * Proj b ρ = Proj b ρ * b := by
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • (1 : A) - b :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hmaps : Set.MapsTo (fun z : ℂ => z • (1 : A) - b) (Metric.sphere (0:ℂ) ρ)
      {x : A | IsUnit x} := fun z hz => hcirc z (by
        have h := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm, sub_zero] at h)
  have hcont : ContinuousOn (Res b) (Metric.sphere (0:ℂ) ρ) := by
    have h := hunits.comp hlin.continuousOn hmaps
    rw [show Res b = Ring.inverse ∘ (fun z : ℂ => z • (1 : A) - b) from rfl]
    exact h
  have hint : CircleIntegrable (Res b) 0 ρ := hcont.circleIntegrable (le_of_lt hρpos)
  have e1 : b * (∮ z in C(0, ρ), Res b z) = ∮ z in C(0, ρ), b * Res b z :=
    (circleIntegral_const_mul b (Res b) 0 ρ hint).symm
  have e2 : (∮ z in C(0, ρ), Res b z) * b = ∮ z in C(0, ρ), Res b z * b :=
    (circleIntegral_mul_const b (Res b) 0 ρ hint).symm
  have e3 : (∮ z in C(0, ρ), b * Res b z) = ∮ z in C(0, ρ), Res b z * b := by
    refine circleIntegral.integral_congr (le_of_lt hρpos) (fun z hz => ?_)
    have hz' : ‖z‖ = ρ := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at h
    exact (res_comm b (hcirc z hz')).symm
  simp only [Proj, CircA]
  rw [mul_smul_comm, smul_mul_assoc, e1, e2, e3]

/-- Deformation invariance: the projection may be computed on the unit circle. -/
theorem spectral_deform (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρle : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    Proj b ρ = ProjB b ρ := by
  have h := (circleIntegral_resolvent_eq b hρpos hρle hunit).1
  simp only [Proj, ProjB, CircA, CircB, Res]
  rw [h]

/-- The projection is idempotent (from the two-circle computation and deformation invariance). -/
theorem spectral_idem (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρle : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b))
    (htwo : CircA b ρ * CircB b ρ = (2 * Real.pi * Complex.I) • CircA b ρ) :
    Proj b ρ * Proj b ρ = Proj b ρ := by
  have h_def : Proj b ρ = ProjB b ρ := spectral_deform b hρpos hρle hunit
  have hc : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (2 * Real.pi * Complex.I) = 1 := by
    rw [inv_mul_cancel₀]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  calc Proj b ρ * Proj b ρ = Proj b ρ * ProjB b ρ := by rw [h_def]
    _ = ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) • (CircA b ρ * CircB b ρ) := by
        simp only [Proj, ProjB]
        rw [smul_mul_smul]
    _ = ((2 * Real.pi * Complex.I)⁻¹ * (2 * Real.pi * Complex.I)⁻¹) •
          ((2 * Real.pi * Complex.I) • CircA b ρ) := by rw [htwo]
    _ = (2 * Real.pi * Complex.I)⁻¹ • CircA b ρ := by
        rw [smul_smul, mul_assoc, hc, mul_one]
    _ = Proj b ρ := rfl

end

end Work.KT.Fund
