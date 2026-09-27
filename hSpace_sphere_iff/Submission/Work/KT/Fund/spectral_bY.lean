import Mathlib
import Submission.Work.KT.Fund.SpectralAux

/-!
# `Work.KT.Fund.spectral_bY` — the left-hand resolvent identity `b * Out = 1 - Proj`

In the abstract setting of a complex Banach algebra `A` (a unital `NormedRing` that is a
`NormedAlgebra ℂ` and complete), let `b : A` have its spectrum off the closed annulus
`ρ ≤ ‖z‖ ≤ 1` (i.e. `z • 1 - b` is a unit for every such `z`), where `0 < ρ < 1`.

Write `Res b z = (z • 1 - b)⁻¹` for the resolvent, `CircA b ρ = ∮_{|z| = ρ} Res b z` for its
circle integral and `Proj b ρ = (2πi)⁻¹ • CircA b ρ` for the "inside" spectral projection.  The
"outside inverse" is `Out b ρ = -(2πi)⁻¹ • ∮_{|z| = ρ} z⁻¹ • Res b z`.

The main result is the left-hand resolvent identity

  `b * Out b ρ = 1 - Proj b ρ`.

The proof is the elementary contour computation: on `|z| = ρ` the resolvent satisfies
`b * Res b z = z • Res b z - 1`, hence

  `b * (∮ z⁻¹ • Res b z) = ∮ (Res b z - z⁻¹ • 1) = CircA b ρ - (2πi) • 1`,

using `∮_{|z| = ρ} z⁻¹ dz = 2πi`; multiplying by `-(2πi)⁻¹` and using
`(2πi)⁻¹ * (2πi) = 1` gives the claim.
-/

namespace Work.KT.Fund

open MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **Pointwise resolvent identity (left).**  Wherever the resolvent of `b` exists,

  `b * Res b z = z • Res b z - 1`,

which is the rearrangement of `b = z • 1 - (z • 1 - b)`. -/
theorem mul_res_bY {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (b : A) {z : ℂ} (hz : IsUnit (z • 1 - b)) :
    b * Res b z = z • Res b z - 1 := by
  have hmul : (z • (1 : A) - b) * Res b z = 1 := by
    rw [Res]
    exact Ring.mul_inverse_cancel _ hz
  have hz' : (z • (1 : A)) * Res b z = z • Res b z := by rw [smul_mul_assoc, one_mul]
  rw [sub_mul, hz'] at hmul
  rw [sub_eq_iff_eq_add] at hmul
  rw [eq_sub_iff_add_eq, hmul, add_comm]

/-- **The contour identity behind `b * Out = 1 - Proj`.**  Pulling `b` inside the circle integral
and using the pointwise resolvent identity,

  `b * ∮_{|z| = ρ} z⁻¹ • Res b z = CircA b ρ - (2πi) • 1`. -/
theorem circleIntegral_b_mul_res_bY {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    b * (∮ z in C(0, ρ), z⁻¹ • Res b z) = CircA b ρ - (2 * Real.pi * Complex.I) • (1 : A) := by
  have hρle : 0 ≤ ρ := le_of_lt hρpos
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  -- points of the circle `|z| = ρ`, the resolvent exists and `z ≠ 0`
  have hsphere : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → ‖z‖ = ρ := by
    intro z hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    exact hz
  have hunit_circle : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → IsUnit (z • 1 - b) := by
    intro z hz
    exact hunit z (le_of_eq (hsphere z hz).symm)
      (le_of_lt (by rw [hsphere z hz]; exact hρlt))
  have hznonzero : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → z ≠ 0 := by
    intro z hz h
    have h0 : ‖z‖ = 0 := by rw [h, norm_zero]
    rw [hsphere z hz] at h0
    linarith
  -- continuity of the resolvent and of `z ↦ z⁻¹` on the circle
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous (fun z : ℂ => z • (1 : A) - b) :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hcont_res : ContinuousOn (fun z : ℂ => Res b z) (Metric.sphere (0 : ℂ) ρ) := by
    have := hunits.comp hlin.continuousOn (fun z hz => hunit_circle z hz)
    simpa only [Res, Function.comp_def] using this
  have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
    ContinuousOn.inv₀ continuousOn_id (fun z hz => hznonzero z hz)
  -- circle integrability of the three integrands
  have hres_int : CircleIntegrable (fun z : ℂ => Res b z) 0 ρ :=
    hcont_res.circleIntegrable hρle
  have hsmul_int : CircleIntegrable (fun z : ℂ => z⁻¹ • Res b z) 0 ρ :=
    (hcont_inv.smul hcont_res).circleIntegrable hρle
  have hzinvone_int : CircleIntegrable (fun z : ℂ => z⁻¹ • (1 : A)) 0 ρ :=
    (hcont_inv.smul continuousOn_const).circleIntegrable hρle
  -- the chain of integral identities
  have h1 : b * (∮ z in C(0, ρ), z⁻¹ • Res b z)
      = ∮ z in C(0, ρ), b * (z⁻¹ • Res b z) :=
    (circleIntegral_const_mul b _ 0 ρ hsmul_int).symm
  have h2 : (∮ z in C(0, ρ), b * (z⁻¹ • Res b z))
      = ∮ z in C(0, ρ), z⁻¹ • (b * Res b z) := by
    apply circleIntegral.integral_congr hρle
    intro z hz
    simp only []
    rw [mul_smul_comm]
  have h3 : (∮ z in C(0, ρ), z⁻¹ • (b * Res b z))
      = ∮ z in C(0, ρ), z⁻¹ • (z • Res b z - 1) := by
    apply circleIntegral.integral_congr hρle
    intro z hz
    simp only []
    rw [mul_res_bY b (hunit_circle z hz)]
  have h4 : (∮ z in C(0, ρ), z⁻¹ • (z • Res b z - 1))
      = ∮ z in C(0, ρ), (Res b z - z⁻¹ • (1 : A)) := by
    apply circleIntegral.integral_congr hρle
    intro z hz
    simp only []
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (hznonzero z hz), one_smul]
  have h5 : (∮ z in C(0, ρ), (Res b z - z⁻¹ • (1 : A)))
      = (∮ z in C(0, ρ), Res b z) - ∮ z in C(0, ρ), z⁻¹ • (1 : A) :=
    circleIntegral.integral_sub hres_int hzinvone_int
  have h6 : (∮ z in C(0, ρ), z⁻¹ • (1 : A)) = (2 * Real.pi * Complex.I) • (1 : A) := by
    rw [circleIntegral.integral_smul_const]
    congr 1
    simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hρne
  rw [CircA, h1, h2, h3, h4, h5, h6]

theorem spectral_bY {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    b * Out b ρ = 1 - Proj b ρ := by
  have hsne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have key := circleIntegral_b_mul_res_bY b hρpos hρlt hunit
  rw [Out, Proj]
  rw [mul_neg]
  rw [mul_smul_comm]
  rw [key]
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [neg_sub]

end

end Work.KT.Fund
