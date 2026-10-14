import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Decay.fderiv_timeHolder
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.bsDeriv_sub_le_of_close =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.CoreResiduals.BiotSavart

open Work.LWP

/-- **The difference of the far-field derivatives of two Biot--Savart fields is bounded by the
sup-distance of the two vorticities on the support ball.**

Let `R > 0`, `M ≥ 0`, `C ≥ 0`, and let `g1 g2 : ℝ³ → ℝ³` be ae-strongly-measurable vorticities, both
bounded by `M` and both supported in the closed ball `B(0,R)`, whose difference obeys
`‖g1 a - g2 a‖ ≤ C` on `B(0,R)`. Then for every `x` with `2R ≤ ‖x‖`,

`‖bsDeriv g1 x - bsDeriv g2 x‖ ≤ (4π)⁻¹ · (C · 4/R³) · (R³ · 4π/3)`,

where `bsDeriv g x = (4π)⁻¹ • ∫ a, crossL (g a) ∘ kDerivCLM (x - a)` is the far-field derivative of
`biotSavart g` (`Work.StabilityFar.Decay.bsDeriv`, which equals `fderiv ℝ (biotSavart g) x` for
`2R ≤ ‖x‖` by `Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far`).

Proof: `bsDeriv` is linear in the vorticity, so the difference is
`(4π)⁻¹ • ∫ a, crossL (g1 a - g2 a) ∘ kDerivCLM (x - a)` (integrability of the two pieces from
`biotSavart_hasFDerivAt_far`); on the support ball the integrand is bounded by `C · 4/R³` (the
pointwise difference bound times `‖kDerivCLM (x-a)‖ ≤ 4/R³`, which holds because `‖x - a‖ ≥ R`), and
it vanishes off the ball (both `gi` vanish there); integrating gives the volume factor `R³·4π/3`.
This is a stripped, single-slice version of the time-Hölder estimate
`Work.StabilityFar.Decay.fderiv_timeHolder`.-/
theorem bsDeriv_sub_le_of_close {R M C : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hC : 0 ≤ C)
    {g1 g2 : Work.LWP.R3 → Work.LWP.R3}
    (h1b : ∀ a, ‖g1 a‖ ≤ M) (h2b : ∀ a, ‖g2 a‖ ≤ M)
    (h1s : ∀ a, g1 a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (h2s : ∀ a, g2 a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (h1m : MeasureTheory.AEStronglyMeasurable g1 MeasureTheory.volume)
    (h2m : MeasureTheory.AEStronglyMeasurable g2 MeasureTheory.volume)
    (hdiff : ∀ a ∈ Metric.closedBall (0 : Work.LWP.R3) R, ‖g1 a - g2 a‖ ≤ C)
    {x : Work.LWP.R3} (hx : 2 * R ≤ ‖x‖) :
    ‖Work.StabilityFar.Decay.bsDeriv g1 x - Work.StabilityFar.Decay.bsDeriv g2 x‖
      ≤ (4 * Real.pi)⁻¹ * (C * (4 / R ^ 3)) * (R ^ 3 * (Real.pi * 4 / 3)) := by
  have hint1 := (Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far hR hM h1b h1s h1m hx).1
  have hint2 := (Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far hR hM h2b h2s h2m hx).1
  have hsub : Work.StabilityFar.Decay.bsDeriv g1 x - Work.StabilityFar.Decay.bsDeriv g2 x
      = (4 * Real.pi)⁻¹ • ∫ a, ((Work.StabilityFar.Decay.crossL (g1 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a))
          - (Work.StabilityFar.Decay.crossL (g2 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a))) := by
    have e1 : Work.StabilityFar.Decay.bsDeriv g1 x = (4 * Real.pi)⁻¹ •
        ∫ a, (Work.StabilityFar.Decay.crossL (g1 a)).comp
          (Work.StabilityFar.Decay.kDerivCLM (x - a)) := rfl
    have e2 : Work.StabilityFar.Decay.bsDeriv g2 x = (4 * Real.pi)⁻¹ •
        ∫ a, (Work.StabilityFar.Decay.crossL (g2 a)).comp
          (Work.StabilityFar.Decay.kDerivCLM (x - a)) := rfl
    have e3 : ∫ a, ((Work.StabilityFar.Decay.crossL (g1 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a))
          - (Work.StabilityFar.Decay.crossL (g2 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a)))
        = (∫ a, (Work.StabilityFar.Decay.crossL (g1 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a)))
          - (∫ a, (Work.StabilityFar.Decay.crossL (g2 a)).comp
            (Work.StabilityFar.Decay.kDerivCLM (x - a))) := integral_sub hint1 hint2
    calc Work.StabilityFar.Decay.bsDeriv g1 x - Work.StabilityFar.Decay.bsDeriv g2 x
        = (4 * Real.pi)⁻¹ • (∫ a, (Work.StabilityFar.Decay.crossL (g1 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a)))
          - (4 * Real.pi)⁻¹ • (∫ a, (Work.StabilityFar.Decay.crossL (g2 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a))) := by rw [e1, e2]
      _ = (4 * Real.pi)⁻¹ • ((∫ a, (Work.StabilityFar.Decay.crossL (g1 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a)))
          - (∫ a, (Work.StabilityFar.Decay.crossL (g2 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a)))) := by rw [smul_sub]
      _ = (4 * Real.pi)⁻¹ • ∫ a, ((Work.StabilityFar.Decay.crossL (g1 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a))
            - (Work.StabilityFar.Decay.crossL (g2 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a))) := by rw [e3]
  rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hintdiff : Integrable (fun a : R3 => (Work.StabilityFar.Decay.crossL (g1 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))
      - (Work.StabilityFar.Decay.crossL (g2 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))) volume := hint1.sub hint2
  have hpt : ∀ a : R3, ‖(Work.StabilityFar.Decay.crossL (g1 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))
      - (Work.StabilityFar.Decay.crossL (g2 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))‖
      ≤ (C * (4 / R ^ 3)) * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a := by
    intro a
    rw [← ContinuousLinearMap.sub_comp, ← Work.StabilityFar.Decay.crossL_sub]
    by_cases ha : a ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem ha, mul_one]
      have haR : ‖a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using ha
      have hxa : R ≤ ‖x - a‖ := by have h := norm_sub_norm_le x a; linarith
      have hK : ‖Work.StabilityFar.Decay.kDerivCLM (x - a)‖ ≤ 4 / R ^ 3 :=
        Work.StabilityFar.Decay.norm_kDerivCLM_le (x - a) R hR hxa
      calc ‖(Work.StabilityFar.Decay.crossL (g1 a - g2 a)).comp
              (Work.StabilityFar.Decay.kDerivCLM (x - a))‖
          ≤ ‖Work.StabilityFar.Decay.crossL (g1 a - g2 a)‖
              * ‖Work.StabilityFar.Decay.kDerivCLM (x - a)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖g1 a - g2 a‖ * (4 / R ^ 3) :=
            mul_le_mul (Work.StabilityFar.Decay.norm_crossL_le _) hK (by positivity)
              (norm_nonneg _)
        _ ≤ C * (4 / R ^ 3) := mul_le_mul_of_nonneg_right (hdiff a ha) (by positivity)
    · rw [Set.indicator_of_notMem ha, mul_zero]
      have h1a : g1 a = 0 := by by_contra h; exact ha (h1s a h)
      have h2a : g2 a = 0 := by by_contra h; exact ha (h2s a h)
      rw [h1a, h2a, sub_zero, Work.StabilityFar.Decay.crossL_zero,
        ContinuousLinearMap.zero_comp, norm_zero]
  have hbndint : Integrable (fun a : R3 => (C * (4 / R ^ 3))
      * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a) volume := by
    have hfin : volume (Metric.closedBall (0 : R3) R) ≠ ⊤ :=
      (isCompact_closedBall 0 R).measure_lt_top.ne
    have hind : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)))
        (volume : Measure R3) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const hfin (by simp)
    exact hind.const_mul _
  have hvol : ∫ a : R3, (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a
      = R ^ 3 * (Real.pi * 4 / 3) := by
    rw [MeasureTheory.integral_indicator measurableSet_closedBall, MeasureTheory.setIntegral_const,
      smul_eq_mul, mul_one]
    exact Work.LWP.BiotSavart.volume_closedBall_real R hR.le
  have h5 : ∫ a, ‖(Work.StabilityFar.Decay.crossL (g1 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))
      - (Work.StabilityFar.Decay.crossL (g2 a)).comp
        (Work.StabilityFar.Decay.kDerivCLM (x - a))‖
      ≤ (C * (4 / R ^ 3)) * (R ^ 3 * (Real.pi * 4 / 3)) := by
    refine (integral_mono_ae hintdiff.norm hbndint (Eventually.of_forall hpt)).trans ?_
    rw [MeasureTheory.integral_const_mul, hvol]
  calc (4 * Real.pi)⁻¹ * ‖∫ a, ((Work.StabilityFar.Decay.crossL (g1 a)).comp
          (Work.StabilityFar.Decay.kDerivCLM (x - a))
        - (Work.StabilityFar.Decay.crossL (g2 a)).comp
          (Work.StabilityFar.Decay.kDerivCLM (x - a)))‖
      ≤ (4 * Real.pi)⁻¹ * ((C * (4 / R ^ 3)) * (R ^ 3 * (Real.pi * 4 / 3))) :=
        mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans h5) (by positivity)
    _ = (4 * Real.pi)⁻¹ * (C * (4 / R ^ 3)) * (R ^ 3 * (Real.pi * 4 / 3)) := by ring

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.StabilityFar.FarDerivLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar


end Work.StabilityFar
end
