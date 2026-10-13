/-
# `Work.StabilityFar.Decay.farField_fderiv_sub_le` — the far-field Lipschitz bound for the
derivative of the Biot–Savart field

For a vorticity `ω` whose time slices are ae-strongly-measurable, uniformly bounded by `M` and
uniformly supported in the closed ball `B(0,R)`, the map `x ↦ fderiv ℝ (biotSavart (ω · t)) x` is
Lipschitz on the far region `{2R ≤ ‖x‖}` with a constant `A` uniform in `t ∈ window T`.

The proof is a single-slice computation, applied at each time `t`.  In the far field the
derivative of the Biot–Savart field is the Bochner integral of the kernel derivative
(`biotSavart_hasFDerivAt_far`), and the difference of two such integrals is bounded by integrating
the difference of the kernel derivatives, which obey the second-order bound
`‖kDerivCLM (x - a) - kDerivCLM (y - a)‖ ≤ 64 R⁻⁴ ‖x - y‖` on the annulus `‖x - a‖, ‖y - a‖ ≥ R`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.FarField
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.norm_crossL_le

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

/-- **The far-field Lipschitz bound for the derivative of the Biot–Savart field.**  For a
space-time vorticity `ω` whose slices are measurable, uniformly bounded by `M` and uniformly
supported in `B(0,R)` on the window `window T`, the map `x ↦ fderiv ℝ (biotSavart (ω · t)) x` is
Lipschitz on the far region `{2R ≤ ‖x‖}` with a constant `A` uniform in `t`. -/
theorem farField_fderiv_sub_le {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3} {R M T : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hmeas : Work.StabilityFar.SlicesMeasurable ω T) (hbdd : Work.StabilityFar.SlicesBounded ω M T)
    (hsupp : Work.StabilityFar.SlicesSupported ω R T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Work.StabilityFar.window T, ∀ x y : Work.StabilityFar.R3,
      2 * R ≤ ‖x‖ → 2 * R ≤ ‖y‖ →
      ‖fderiv ℝ (Work.LWP.biotSavart (ω · t)) x - fderiv ℝ (Work.LWP.biotSavart (ω · t)) y‖
        ≤ A * ‖x - y‖ := by
  refine ⟨(4 * Real.pi)⁻¹ * ((M * 64 / R ^ 4) * (R ^ 3 * (Real.pi * 4 / 3))),
    by positivity, ?_⟩
  intro t ht x y hx hy
  have hda := biotSavart_hasFDerivAt_far (ω := (ω · t)) hR hM
    (fun a => hbdd t ht a) (fun a => hsupp t ht a) (hmeas t ht) hx
  have hdb := biotSavart_hasFDerivAt_far (ω := (ω · t)) hR hM
    (fun a => hbdd t ht a) (fun a => hsupp t ht a) (hmeas t ht) hy
  rw [hda.2.fderiv, hdb.2.fderiv]
  exact norm_bsDeriv_sub_le (ω := (ω · t)) hR hM
    (fun a => hbdd t ht a) (fun a => hsupp t ht a) (hmeas t ht) hx hy

end Work.StabilityFar.Decay
