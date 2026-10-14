import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const
import Submission.Work.LWP.Main
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.St5
-- ===== merged: Submission.Work.StabilityFar.Decay.farField_fderiv_sub_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.StabilityFar.Decay

open Work.LWP

/-- **Single-slice far-field Lipschitz bound.**  For a measurable, uniformly bounded, supported
vorticity, the derivative of its Biot–Savart field is Lipschitz on `{2R ≤ ‖·‖}` with constant
`32 M / R`. -/
theorem norm_bsDeriv_sub_le {ω : R3 → R3} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hω : ∀ a, ‖ω a‖ ≤ M) (hsupp : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x y : R3} (hx : 2 * R ≤ ‖x‖) (hy : 2 * R ≤ ‖y‖) :
    ‖bsDeriv ω x - bsDeriv ω y‖
      ≤ ((4 * Real.pi)⁻¹ * ((M * 64 / R ^ 4) * (R ^ 3 * (Real.pi * 4 / 3)))) * ‖x - y‖ := by
  have hintx := (biotSavart_hasFDerivAt_far hR hM hω hsupp hmeas hx).1
  have hinty := (biotSavart_hasFDerivAt_far hR hM hω hsupp hmeas hy).1
  have hsub : bsDeriv ω x - bsDeriv ω y
      = (4 * Real.pi)⁻¹ • ∫ a, ((crossL (ω a)).comp (kDerivCLM (x - a))
          - (crossL (ω a)).comp (kDerivCLM (y - a))) := by
    have e1 : bsDeriv ω x = (4 * Real.pi)⁻¹ •
        ∫ a, (crossL (ω a)).comp (kDerivCLM (x - a)) := rfl
    have e2 : bsDeriv ω y = (4 * Real.pi)⁻¹ •
        ∫ a, (crossL (ω a)).comp (kDerivCLM (y - a)) := rfl
    have e3 : ∫ a, ((crossL (ω a)).comp (kDerivCLM (x - a))
        - (crossL (ω a)).comp (kDerivCLM (y - a)))
        = (∫ a, (crossL (ω a)).comp (kDerivCLM (x - a)))
          - (∫ a, (crossL (ω a)).comp (kDerivCLM (y - a))) := integral_sub hintx hinty
    calc bsDeriv ω x - bsDeriv ω y
        = (4 * Real.pi)⁻¹ • (∫ a, (crossL (ω a)).comp (kDerivCLM (x - a)))
          - (4 * Real.pi)⁻¹ • (∫ a, (crossL (ω a)).comp (kDerivCLM (y - a))) := by rw [e1, e2]
      _ = (4 * Real.pi)⁻¹ • ((∫ a, (crossL (ω a)).comp (kDerivCLM (x - a)))
          - (∫ a, (crossL (ω a)).comp (kDerivCLM (y - a)))) := by rw [smul_sub]
      _ = (4 * Real.pi)⁻¹ • ∫ a, ((crossL (ω a)).comp (kDerivCLM (x - a))
          - (crossL (ω a)).comp (kDerivCLM (y - a))) := by rw [e3]
  rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hpt : ∀ a : R3, ‖(crossL (ω a)).comp (kDerivCLM (x - a))
        - (crossL (ω a)).comp (kDerivCLM (y - a))‖
      ≤ (M * 64 / R ^ 4 * ‖x - y‖)
        * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a := by
    intro a
    by_cases ha : a ∈ Metric.closedBall (0 : R3) R
    · rw [Set.indicator_of_mem ha, mul_one]
      have haR : ‖a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using ha
      have hxa : R ≤ ‖x - a‖ := by have := norm_sub_norm_le x a; linarith
      have hya : R ≤ ‖y - a‖ := by have := norm_sub_norm_le y a; linarith
      have h2 : ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖ ≤ 64 / R ^ 4 * ‖x - y‖ := by
        have := norm_kDerivCLM_sub_le (x - a) (y - a) R hR hxa hya
        rwa [show (x - a) - (y - a) = x - y by abel] at this
      rw [← ContinuousLinearMap.comp_sub]
      calc ‖(crossL (ω a)).comp (kDerivCLM (x - a) - kDerivCLM (y - a))‖
          ≤ ‖crossL (ω a)‖ * ‖kDerivCLM (x - a) - kDerivCLM (y - a)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖ω a‖ * (64 / R ^ 4 * ‖x - y‖) :=
            mul_le_mul (norm_crossL_le (ω a)) h2 (by positivity) (norm_nonneg _)
        _ ≤ M * (64 / R ^ 4 * ‖x - y‖) :=
            mul_le_mul_of_nonneg_right (hω a) (by positivity)
        _ = M * 64 / R ^ 4 * ‖x - y‖ := by ring
    · rw [Set.indicator_of_notMem ha, mul_zero]
      have hωa : ω a = 0 := by by_contra h; exact ha (hsupp a h)
      rw [hωa, crossL_zero, ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_comp,
        sub_zero, norm_zero]
  have hintdiff : Integrable (fun a : R3 => (crossL (ω a)).comp (kDerivCLM (x - a))
      - (crossL (ω a)).comp (kDerivCLM (y - a))) volume := hintx.sub hinty
  have hbndint : Integrable (fun a : R3 => (M * 64 / R ^ 4 * ‖x - y‖)
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
  have h5 : ∫ a, ‖(crossL (ω a)).comp (kDerivCLM (x - a))
      - (crossL (ω a)).comp (kDerivCLM (y - a))‖
      ≤ (M * 64 / R ^ 4 * ‖x - y‖) * (R ^ 3 * (Real.pi * 4 / 3)) := by
    refine (integral_mono_ae hintdiff.norm hbndint
      (Filter.Eventually.of_forall hpt)).trans ?_
    rw [MeasureTheory.integral_const_mul, hvol]
  have heq : (4 * Real.pi)⁻¹ * ((M * 64 / R ^ 4 * ‖x - y‖) * (R ^ 3 * (Real.pi * 4 / 3)))
      = ((4 * Real.pi)⁻¹ * ((M * 64 / R ^ 4) * (R ^ 3 * (Real.pi * 4 / 3)))) * ‖x - y‖ := by
    ring
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans h5) (by positivity) |>.trans (le_of_eq heq)


end Work.StabilityFar.Decay
end
-- ===== merged: Submission.Work.StabilityFar.Decay.fderiv_timeHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory


end Work.StabilityFar.Decay
end
