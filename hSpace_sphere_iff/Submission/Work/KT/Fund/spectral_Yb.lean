import Mathlib
import Submission.Work.KT.Fund.SpectralAux

/-!
# `Work.KT.Fund.spectral_Yb` — the right-hand resolvent identity `Out * b = 1 - Proj`

In the abstract setting of a complex Banach algebra `A` (a unital `NormedRing` that is a
`NormedAlgebra ℂ` and complete), let `b : A` have its spectrum off the closed annulus
`ρ ≤ ‖z‖ ≤ 1` (i.e. `z • 1 - b` is a unit for every such `z`), where `0 < ρ < 1`.

Write `Res b z = (z • 1 - b)⁻¹` for the resolvent, `CircA b ρ = ∮_{|z| = ρ} Res b z` for its
circle integral and `Proj b ρ = (2πi)⁻¹ • CircA b ρ` for the "inside" spectral projection.  The
"outside inverse" is `Out b ρ = -(2πi)⁻¹ • ∮_{|z| = ρ} z⁻¹ • Res b z`.

The main result is the right-hand resolvent identity

  `Out b ρ * b = 1 - Proj b ρ`.

The proof is the elementary contour computation: on `|z| = ρ` the resolvent satisfies
`Res b z * b = z • Res b z - 1`, hence

  `(∮ z⁻¹ • Res b z) * b = ∮ (Res b z - z⁻¹ • 1) = CircA b ρ - (2πi) • 1`,

using `∮_{|z| = ρ} z⁻¹ dz = 2πi`; multiplying by `-(2πi)⁻¹` and using
`(2πi)⁻¹ * (2πi) = 1` gives the claim.
-/

namespace Work.KT.Fund

open MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Pointwise resolvent identity.**  Wherever the resolvent of `b` exists,

  `Res b z * b = z • Res b z - 1`,

which is the rearrangement of `b = z • 1 - (z • 1 - b)`. -/
theorem res_mul_self (b : A) {z : ℂ} (hz : IsUnit (z • 1 - b)) :
    Res b z * b = z • Res b z - 1 := by
  have h1 : Ring.inverse (z • 1 - b) * (z • 1 - b) = 1 := Ring.inverse_mul_cancel _ hz
  have hz1 : Ring.inverse (z • 1 - b) * (z • 1) = z • Ring.inverse (z • 1 - b) := by
    rw [mul_smul_comm, mul_one]
  have h2 : b + (z • (1 : A) - b) = z • (1 : A) := by abel
  have key : Ring.inverse (z • 1 - b) * b + 1 = z • Ring.inverse (z • 1 - b) := by
    calc Ring.inverse (z • 1 - b) * b + 1
        = Ring.inverse (z • 1 - b) * b + Ring.inverse (z • 1 - b) * (z • 1 - b) := by
          rw [h1]
      _ = Ring.inverse (z • 1 - b) * (b + (z • 1 - b)) := by rw [mul_add]
      _ = Ring.inverse (z • 1 - b) * (z • 1) := by rw [h2]
      _ = z • Ring.inverse (z • 1 - b) := hz1
  simp only [Res]
  exact (sub_eq_iff_eq_add.mpr key.symm).symm

theorem spectral_Yb {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    Out b ρ * b = 1 - Proj b ρ := by
  have hρle : 0 ≤ ρ := le_of_lt hρpos
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  -- The resolvent is continuous on the circle `|z| = ρ`.
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous (fun z : ℂ => z • (1 : A) - b) :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hcirc : ∀ z : ℂ, ‖z‖ = ρ → IsUnit (z • 1 - b) := fun z hz =>
    hunit z (le_of_eq hz.symm) (by rw [hz]; exact le_of_lt hρlt)
  have hmaps : Set.MapsTo (fun z : ℂ => z • (1 : A) - b) (Metric.sphere (0 : ℂ) ρ)
      {x : A | IsUnit x} := fun z hz =>
    hcirc z (by
      have hz' := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at hz')
  have hcontRes : ContinuousOn (Res b) (Metric.sphere (0 : ℂ) ρ) :=
    hunits.comp hlin.continuousOn hmaps
  have hRes_int : CircleIntegrable (Res b) 0 ρ := hcontRes.circleIntegrable hρle
  -- `z⁻¹` is continuous on the circle `|z| = ρ` (which avoids the origin).
  have hinvc : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro z hz
    show z ≠ 0
    have hz' : ‖z‖ = ρ := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at h
    intro h
    rw [h, norm_zero] at hz'
    exact hρne hz'.symm
  have hf1 : CircleIntegrable (fun z : ℂ => z⁻¹ • Res b z) 0 ρ :=
    (hinvc.smul hcontRes).circleIntegrable hρle
  have hf3 : CircleIntegrable (fun z : ℂ => z⁻¹ • (1 : A)) 0 ρ :=
    (hinvc.smul continuousOn_const).circleIntegrable hρle
  -- The main contour computation.
  have hYb : (∮ z in C(0, ρ), z⁻¹ • Res b z) * b
      = CircA b ρ - (2 * Real.pi * Complex.I) • (1 : A) := by
    have step1 : (∮ z in C(0, ρ), z⁻¹ • Res b z) * b
        = ∮ z in C(0, ρ), (z⁻¹ • Res b z) * b :=
      (circleIntegral_mul_const b (fun z => z⁻¹ • Res b z) 0 ρ hf1).symm
    have step2 : (∮ z in C(0, ρ), (z⁻¹ • Res b z) * b)
        = ∮ z in C(0, ρ), (Res b z - z⁻¹ • (1 : A)) :=
      circleIntegral.integral_congr hρle (fun z hz => by
        have hz' : ‖z‖ = ρ := by
          have h := Metric.mem_sphere.mp hz
          rwa [dist_eq_norm, sub_zero] at h
        have hz0 : z ≠ 0 := by
          intro h
          rw [h, norm_zero] at hz'
          exact hρne hz'.symm
        rw [smul_mul_assoc, res_mul_self b (hcirc z hz'), smul_sub, smul_smul,
          inv_mul_cancel₀ hz0, one_smul])
    have step3 : (∮ z in C(0, ρ), (Res b z - z⁻¹ • (1 : A)))
        = CircA b ρ - (2 * Real.pi * Complex.I) • (1 : A) := by
      rw [circleIntegral.integral_sub hRes_int hf3]
      rw [circleIntegral.integral_smul_const (fun z => z⁻¹) (1 : A) 0 ρ]
      rw [show (∮ z in C(0, ρ), z⁻¹) = 2 * Real.pi * Complex.I from by
        simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hρne]
      simp only [CircA]
    rw [step1, step2, step3]
  -- `(2πi)⁻¹ * (2πi) = 1`.
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hc : (2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I) = 1 :=
    inv_mul_cancel₀ hne
  rw [Out, neg_mul, smul_mul_assoc, hYb, smul_sub, neg_sub, smul_smul, hc, one_smul, Proj]

end

end Work.KT.Fund
