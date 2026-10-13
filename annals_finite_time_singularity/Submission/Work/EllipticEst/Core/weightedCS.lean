import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

theorem weightedCS {s : Set ℝ} (hs : MeasurableSet s) {w g : ℝ → ℝ}
    (hw : ∀ t ∈ s, 0 < w t) (hwc : ContinuousOn w s) (hgc : ContinuousOn g s)
    (hg2 : MeasureTheory.IntegrableOn (fun t => (g t) ^ 2 * w t) s)
    (hwi : MeasureTheory.IntegrableOn (fun t => (w t)⁻¹) s) :
    (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => g t)) ^ 2
      ≤ (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => (g t) ^ 2 * w t))
        * (MeasureTheory.integral (MeasureTheory.volume.restrict s) (fun t => (w t)⁻¹)) := by
  have hsw : ContinuousOn (fun t => Real.sqrt (w t)) s :=
    Real.continuous_sqrt.comp_continuousOn hwc
  have hpos : ∀ t ∈ s, 0 < Real.sqrt (w t) := fun t ht => Real.sqrt_pos.2 (hw t ht)
  have hne : ∀ t ∈ s, Real.sqrt (w t) ≠ 0 := fun t ht => ne_of_gt (hpos t ht)
  have hwge : ∀ t ∈ s, 0 ≤ w t := fun t ht => (hw t ht).le
  have hu_aesm : MeasureTheory.AEStronglyMeasurable (fun t => g t * Real.sqrt (w t))
      (MeasureTheory.volume.restrict s) :=
    (hgc.mul hsw).aestronglyMeasurable hs
  have hu_mem : MeasureTheory.MemLp (fun t => g t * Real.sqrt (w t)) 2
      (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hu_aesm]
    refine hg2.congr_fun ?_ hs
    intro t ht
    change g t ^ 2 * w t = (g t * Real.sqrt (w t)) ^ 2
    rw [mul_pow, Real.sq_sqrt (hwge t ht)]
  have hv_aesm : MeasureTheory.AEStronglyMeasurable (fun t => (Real.sqrt (w t))⁻¹)
      (MeasureTheory.volume.restrict s) :=
    (hsw.inv₀ hne).aestronglyMeasurable hs
  have hv_mem : MeasureTheory.MemLp (fun t => (Real.sqrt (w t))⁻¹) 2
      (MeasureTheory.volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hv_aesm]
    refine hwi.congr_fun ?_ hs
    intro t ht
    change (w t)⁻¹ = ((Real.sqrt (w t))⁻¹) ^ 2
    rw [inv_pow, Real.sq_sqrt (hwge t ht)]
  have h_uv : (∫ t in s, (g t * Real.sqrt (w t)) * (Real.sqrt (w t))⁻¹) = ∫ t in s, g t :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one])
  have h_u2 : (∫ t in s, (g t * Real.sqrt (w t)) ^ 2) = ∫ t in s, g t ^ 2 * w t :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [mul_pow, Real.sq_sqrt (hwge t ht)])
  have h_v2 : (∫ t in s, ((Real.sqrt (w t))⁻¹) ^ 2) = ∫ t in s, (w t)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun hs (fun t ht => by
      rw [inv_pow, Real.sq_sqrt (hwge t ht)])
  have key := Work.Spaces.cs_integral hu_mem hv_mem
  rw [h_uv, h_u2, h_v2] at key
  exact key

end Work.EllipticEst.Core
