import Mathlib
import Submission.Work.KT.Fund.SpectralAux
import Submission.Work.KT.Fund.SpectralBasic
import Submission.Work.KT.Fund.circleIntegral_inv_sub_eq_zero

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The resolvent is continuous on a circle lying in its domain. -/
theorem res_continuousOn (b : A) {r : ℝ} (hunit : ∀ z : ℂ, ‖z‖ = r → IsUnit (z • 1 - b)) :
    ContinuousOn (Res b) (Metric.sphere (0:ℂ) r) := by
  have hunits : ContinuousOn Ring.inverse {x : A | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • (1 : A) - b :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hmaps : Set.MapsTo (fun z : ℂ => z • (1 : A) - b) (Metric.sphere (0:ℂ) r)
      {x : A | IsUnit x} := fun z hz => hunit z (by
        have h := Metric.mem_sphere.mp hz
        rwa [dist_eq_norm, sub_zero] at h)
  have h := hunits.comp hlin.continuousOn hmaps
  rw [show Res b = Ring.inverse ∘ (fun z : ℂ => z • (1 : A) - b) from rfl]
  exact h

/-- **The two-circle computation**: `CircA * CircB = 2πi • CircA` for a resolvent that is
unitary on the annulus `ρ ≤ ‖z‖ ≤ 1` with `0 < ρ < 1`. -/
theorem twoRadius_alt (b : A) {ρ : ℝ} (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • 1 - b)) :
    CircA b ρ * CircB b ρ = (2 * Real.pi * Complex.I) • CircA b ρ := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρpos
  have hone0 : (0:ℝ) ≤ 1 := by norm_num
  have hsphere : ∀ (r : ℝ) (z : ℂ), z ∈ Metric.sphere (0:ℂ) r → ‖z‖ = r := by
    intro r z hz
    have h := Metric.mem_sphere.mp hz
    rwa [dist_eq_norm, sub_zero] at h
  have hcontρ : ContinuousOn (Res b) (Metric.sphere (0:ℂ) ρ) :=
    res_continuousOn b (fun z hz => hunit z (le_of_eq hz.symm) (by rw [hz]; exact le_of_lt hρlt))
  have hcont1 : ContinuousOn (Res b) (Metric.sphere (0:ℂ) 1) :=
    res_continuousOn b (fun z hz => hunit z (by rw [hz]; exact le_of_lt hρlt) (le_of_eq hz))
  have hintρ : CircleIntegrable (Res b) 0 ρ := hcontρ.circleIntegrable hρ0
  have hint1 : CircleIntegrable (Res b) 0 1 := hcont1.circleIntegrable hone0
  -- points distinct in norm give a nonzero denominator
  have hneq : ∀ w w' : ℂ, ‖w‖ = ρ → ‖w'‖ = 1 → w' - w ≠ 0 := by
    intro w w' hw hw' h0
    have h : w' = w := sub_eq_zero.mp h0
    rw [h, hw] at hw'
    linarith
  -- joint continuity of the Fubini kernel
  have hsw : ContinuousOn (Function.uncurry fun w w' : ℂ => (w' - w)⁻¹ • (Res b w - Res b w'))
      (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) 1) := by
    have hne : ∀ p ∈ (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) 1), p.2 - p.1 ≠ 0 := by
      rintro ⟨w, w'⟩ ⟨hw, hw'⟩ h0
      exact hneq w w' (hsphere ρ w hw) (hsphere 1 w' hw') h0
    have hf : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹)
        (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) 1) :=
      ContinuousOn.inv₀ (by fun_prop) hne
    have hg : ContinuousOn (fun p : ℂ × ℂ => Res b p.1 - Res b p.2)
        (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) 1) :=
      (hcontρ.comp continuous_fst.continuousOn (fun p hp => hp.1)).sub
        (hcont1.comp continuous_snd.continuousOn (fun p hp => hp.2))
    exact ContinuousOn.smul hf hg
  -- the pointwise resolvent identity on the two circles
  have hpoint : ∀ w w' : ℂ, ‖w‖ = ρ → ‖w'‖ = 1 →
      Res b w * Res b w' = (w' - w)⁻¹ • (Res b w - Res b w') := by
    intro w w' hw hw'
    have hunw : IsUnit (w • 1 - b) := hunit w (le_of_eq hw.symm) (by rw [hw]; exact le_of_lt hρlt)
    have hunw' : IsUnit (w' • 1 - b) := hunit w' (by rw [hw']; exact le_of_lt hρlt) (le_of_eq hw')
    have hne : w' - w ≠ 0 := hneq w w' hw hw'
    have hcw : (w' • 1 - b) * Res b w = Res b w * (w' • 1 - b) := by
      rw [sub_mul, smul_mul_assoc, one_mul, mul_sub, mul_smul_comm, mul_one, res_comm b hunw]
    have k1 : (w' • 1 - b) * (Res b w * Res b w') = Res b w := by
      rw [← mul_assoc, hcw, mul_assoc,
        show Res b w' = Ring.inverse (w' • 1 - b) from rfl, Ring.mul_inverse_cancel _ hunw',
        mul_one]
    have k2 : (w • 1 - b) * (Res b w * Res b w') = Res b w' := by
      rw [← mul_assoc, show Res b w = Ring.inverse (w • 1 - b) from rfl,
        Ring.mul_inverse_cancel _ hunw, one_mul]
    have k4 : ((w' • 1 - b) - (w • 1 - b)) = (w' - w) • (1 : A) := by
      rw [sub_sub_sub_cancel_right, ← sub_smul]
    have k3 : Res b w - Res b w' = (w' - w) • (Res b w * Res b w') := by
      calc Res b w - Res b w'
          = ((w' • 1 - b) - (w • 1 - b)) * (Res b w * Res b w') := by rw [sub_mul, k1, k2]
        _ = ((w' - w) • (1 : A)) * (Res b w * Res b w') := by rw [k4]
        _ = (w' - w) • (Res b w * Res b w') := by rw [smul_mul_assoc, one_mul]
    rw [k3]
    exact (inv_smul_smul₀ hne (Res b w * Res b w')).symm
  -- the scalar vanishing
  have hzero : ∀ w' : ℂ, ‖w'‖ = 1 → (∮ w in C(0, ρ), (w' - w)⁻¹) = 0 := by
    intro w' hw'
    have h3 : (∮ w in C(0, ρ), (w - w')⁻¹) = 0 :=
      circleIntegral_inv_sub_eq_zero hρpos (by rw [hw']; exact hρlt)
    have h4 : (∮ w in C(0, ρ), (w' - w)⁻¹) = ∮ w in C(0, ρ), (-1 : ℂ) • (w - w')⁻¹ := by
      refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
      rw [show w' - w = -(w - w') from by ring, inv_neg, neg_one_smul]
    rw [h4, circleIntegral.integral_smul, h3, smul_zero]
  -- step 1: split the double integral
  have step1 : CircA b ρ * CircB b ρ
      = ∮ w in C(0, ρ), ∮ w' in C(0, 1), Res b w * Res b w' := by
    have s1 : (∮ w in C(0, ρ), ∮ w' in C(0, 1), Res b w * Res b w')
        = ∮ w in C(0, ρ), Res b w * ∮ w' in C(0, 1), Res b w' := by
      refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
      exact circleIntegral_const_mul (Res b w) (Res b) 0 1 hint1
    have s2 : (∮ w in C(0, ρ), Res b w * ∮ w' in C(0, 1), Res b w')
        = (∮ w in C(0, ρ), Res b w) * ∮ w' in C(0, 1), Res b w' :=
      circleIntegral_mul_const (∮ w' in C(0, 1), Res b w') (Res b) 0 ρ hintρ
    rw [CircA, CircB]
    exact (s1.trans s2).symm
  -- step 2: replace the product by the resolvent identity
  have step2 : (∮ w in C(0, ρ), ∮ w' in C(0, 1), Res b w * Res b w')
      = ∮ w in C(0, ρ), ∮ w' in C(0, 1), (w' - w)⁻¹ • (Res b w - Res b w') := by
    refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
    refine circleIntegral.integral_congr hone0 (fun w' hw' => ?_)
    exact hpoint w w' (hsphere ρ w hw) (hsphere 1 w' hw')
  -- step 3: swap the two circle integrals (Fubini)
  have step3 : (∮ w in C(0, ρ), ∮ w' in C(0, 1), (w' - w)⁻¹ • (Res b w - Res b w'))
      = ∮ w' in C(0, 1), ∮ w in C(0, ρ), (w' - w)⁻¹ • (Res b w - Res b w') :=
    circleIntegral_swap _ hρ0 hone0 hsw
  -- step 4: the second term vanishes
  have step4 : (∮ w' in C(0, 1), ∮ w in C(0, ρ), (w' - w)⁻¹ • (Res b w - Res b w'))
      = ∮ w' in C(0, 1), ∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w := by
    refine circleIntegral.integral_congr hone0 (fun w' hw' => ?_)
    have hw'1 : ‖w'‖ = 1 := hsphere 1 w' hw'
    have hA : CircleIntegrable (fun w : ℂ => (w' - w)⁻¹ • Res b w) 0 ρ := by
      refine ContinuousOn.circleIntegrable hρ0 ?_
      refine ContinuousOn.smul ?_ hcontρ
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro w hw h0
      exact hneq w w' (hsphere ρ w hw) hw'1 h0
    have hB : CircleIntegrable (fun w : ℂ => (w' - w)⁻¹ • Res b w') 0 ρ := by
      refine ContinuousOn.circleIntegrable hρ0 ?_
      refine ContinuousOn.smul ?_ continuousOn_const
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      intro w hw h0
      exact hneq w w' (hsphere ρ w hw) hw'1 h0
    have hInt : (∮ w in C(0, ρ), (w' - w)⁻¹ • (Res b w - Res b w'))
        = (∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w)
          - (∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w') := by
      rw [← circleIntegral.integral_sub hA hB]
      refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
      rw [smul_sub]
    rw [hInt]
    have hz : (∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w') = 0 := by
      rw [circleIntegral.integral_smul_const (fun w : ℂ => (w' - w)⁻¹) (Res b w') 0 ρ,
        hzero w' hw'1, zero_smul]
    rw [hz, sub_zero]
  -- step 5: evaluate the Cauchy integral over the unit circle
  have step5 : (∮ w' in C(0, 1), ∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w)
      = (2 * Real.pi * Complex.I) • CircA b ρ := by
    have hcont2 : ContinuousOn (Function.uncurry fun w w' : ℂ => (w' - w)⁻¹ • Res b w)
        (Metric.sphere (0:ℂ) ρ ×ˢ Metric.sphere (0:ℂ) 1) := by
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.inv₀ (by fun_prop) ?_
        rintro ⟨w, w'⟩ ⟨hw, hw'⟩ h0
        exact hneq w w' (hsphere ρ w hw) (hsphere 1 w' hw') h0
      · exact hcontρ.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have hsw2 : (∮ w' in C(0, 1), ∮ w in C(0, ρ), (w' - w)⁻¹ • Res b w)
        = ∮ w in C(0, ρ), ∮ w' in C(0, 1), (w' - w)⁻¹ • Res b w :=
      (circleIntegral_swap (fun w w' : ℂ => (w' - w)⁻¹ • Res b w) hρ0 hone0 hcont2).symm
    rw [hsw2]
    have e1 : (∮ w in C(0, ρ), ∮ w' in C(0, 1), (w' - w)⁻¹ • Res b w)
        = ∮ w in C(0, ρ), (∮ w' in C(0, 1), (w' - w)⁻¹) • Res b w := by
      refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
      exact circleIntegral.integral_smul_const (fun w' : ℂ => (w' - w)⁻¹) (Res b w) 0 1
    have e2 : (∮ w in C(0, ρ), (∮ w' in C(0, 1), (w' - w)⁻¹) • Res b w)
        = ∮ w in C(0, ρ), (2 * Real.pi * Complex.I) • Res b w := by
      refine circleIntegral.integral_congr hρ0 (fun w hw => ?_)
      have hw1 : w ∈ Metric.ball (0:ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, hsphere ρ w hw]
        exact hρlt
      rw [circleIntegral.integral_sub_inv_of_mem_ball hw1]
    rw [e1, e2, circleIntegral.integral_smul]
    rfl
  rw [step1, step2, step3, step4, step5]

end

end Work.KT.Fund
