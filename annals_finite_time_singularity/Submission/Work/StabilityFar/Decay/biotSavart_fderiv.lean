/-
# `Work.StabilityFar.Decay.biotSavart_fderiv` — differentiability of the Biot–Savart field in the
far field, with the explicit derivative

For a vorticity `ω` that is ae-strongly-measurable, bounded by `M` and supported in the closed
ball `B(0,R)`, the field `biotSavart ω` is differentiable at every point `x` with `‖x‖ ≥ 2R`,
with derivative the Bochner integral of the derivatives of the Biot–Savart integrand:

  `fderiv ℝ (biotSavart ω) x = bsDeriv ω x = (4π)⁻¹ • ∫ a, crossL (ω a) ∘ kDerivCLM (x - a)`,
  `Integrable (fun a ↦ crossL (ω a) ∘ kDerivCLM (x - a))`.

This is proved by differentiating under the integral sign
(`hasFDerivAt_integral_of_dominated_loc_of_lip`): the integrand `y ↦ ‖y - a‖⁻³ (ω a × (y - a))` is
Lipschitz in `y` on a ball around `x` uniformly in `a` (the far-field estimate `bsK_diff_le`, whose
constant is integrable after restricting to the (finite-measure) support ball), and its derivative
in `y` is the explicit kernel `crossL (ω a) ∘ kDerivCLM (x - a)`.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.kf_hasFDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.StabilityFar.Decay

open Work.LWP

lemma crossL_zero : crossL (0 : R3) = 0 := by
  ext v; rw [crossL_apply]; simp

/-- Pointwise derivative of the Biot–Savart integrand `y ↦ bsK ω y a` in its `y`-argument. -/
theorem bsK_hasFDerivAt (ω : R3 → R3) (x a : R3) (hxa : x ≠ a) :
    HasFDerivAt (fun y : R3 => Work.LWP.BiotSavart.bsK ω y a)
      ((crossL (ω a)).comp (kDerivCLM (x - a))) x := by
  have hxd : x - a ≠ 0 := sub_ne_zero.mpr hxa
  have hk : HasFDerivAt (fun y : R3 => kf (y - a)) (kDerivCLM (x - a)) x := by
    have h1 : HasFDerivAt (fun y : R3 => y - a) (ContinuousLinearMap.id ℝ R3) x := by
      simpa using (hasFDerivAt_id x).sub_const a
    exact (kf_hasFDerivAt (x - a) hxd).comp x h1
  have h2 : HasFDerivAt (fun y : R3 => crossL (ω a) (kf (y - a)))
      ((crossL (ω a)).comp (kDerivCLM (x - a))) x :=
    (ContinuousLinearMap.hasFDerivAt (crossL (ω a))).comp x hk
  have heq : (fun y : R3 => Work.LWP.BiotSavart.bsK ω y a)
      = fun y : R3 => crossL (ω a) (kf (y - a)) := by
    funext y; exact bsK_eq_crossL ω y a
  rwa [heq]

/-- Differentiability of the Biot–Savart field in the far field, with the explicit derivative and
integrability of the derivative integrand. -/
theorem biotSavart_hasFDerivAt_far {ω : R3 → R3} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hω : ∀ a, ‖ω a‖ ≤ M)
    (hsupp : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hmeas : AEStronglyMeasurable ω volume) {x : R3} (hx : 2 * R ≤ ‖x‖) :
    Integrable (fun a : R3 => (crossL (ω a)).comp (kDerivCLM (x - a)))
      ∧ HasFDerivAt (Work.LWP.biotSavart ω) (bsDeriv ω x) x := by
  have hxR : R < ‖x‖ := by linarith
  set bound : R3 → ℝ := fun a =>
    ((1030 * 64) * M / ‖x‖ ^ 3) * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) a
    with hbound
  have hCnn : 0 ≤ (1030 * 64) * M / ‖x‖ ^ 3 := by positivity
  have hlip : ∀ᵐ a ∂(volume : Measure R3),
      LipschitzOnWith (Real.nnabs (bound a)) (fun y : R3 => Work.LWP.BiotSavart.bsK ω y a)
        (Metric.ball x (R / 2)) := by
    refine Filter.Eventually.of_forall fun a => ?_
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro z hz z' hz'
    rw [Real.coe_nnabs]
    by_cases ha : a ∈ Metric.closedBall (0 : R3) R
    · have hbounda : bound a = (1030 * 64) * M / ‖x‖ ^ 3 := by
        rw [hbound]; simp [Set.indicator_of_mem ha]
      rw [hbounda, abs_of_nonneg hCnn]
      have hsub : Metric.ball x (R / 2) ⊆ Metric.ball x (‖x‖ / 4) :=
        Metric.ball_subset_ball (by linarith)
      have h1 := Work.LWP.BiotSavart.bsK_diff_le hM hω hsupp hx (hsub hz) (hsub hz') a
      rw [dist_eq_norm, dist_eq_norm]
      exact h1
    · have hbounda : bound a = 0 := by
        rw [hbound]; simp [Set.indicator_of_notMem ha]
      rw [hbounda, abs_zero, zero_mul]
      have hωa : ω a = 0 := by
        by_contra h; exact ha (hsupp a h)
      rw [Work.LWP.BiotSavart.bsK_eq_zero hωa, Work.LWP.BiotSavart.bsK_eq_zero hωa]
      simp
  have hbound_int : Integrable bound (volume : Measure R3) := by
    rw [hbound]
    have hfin : (volume : Measure R3) (Metric.closedBall (0 : R3) R) ≠ ⊤ :=
      (isCompact_closedBall 0 R).measure_lt_top.ne
    have hind : Integrable ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)))
        (volume : Measure R3) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const hfin (by simp)
    exact hind.const_mul _
  have hdiff : ∀ᵐ a ∂(volume : Measure R3),
      HasFDerivAt (fun y : R3 => Work.LWP.BiotSavart.bsK ω y a)
        ((crossL (ω a)).comp (kDerivCLM (x - a))) x := by
    have hne : ∀ᵐ a ∂(volume : Measure R3), a ≠ x := by
      rw [MeasureTheory.ae_iff]; simpa using measure_singleton x
    exact hne.mono fun a ha => bsK_hasFDerivAt ω x a (Ne.symm ha)
  have hmain := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := (volume : Measure R3))
    (F := fun y a => Work.LWP.BiotSavart.bsK ω y a)
    (F' := fun a => (crossL (ω a)).comp (kDerivCLM (x - a)))
    (s := Metric.ball x (R / 2)) (x₀ := x) (bound := bound)
    (Metric.ball_mem_nhds x (by positivity))
    (Filter.Eventually.of_forall fun y => Work.LWP.BiotSavart.aestronglyMeasurable_bsK hmeas y)
    (Work.LWP.BiotSavart.integrable_bsK hM hω hsupp hmeas hxR)
    (aestronglyMeasurable_bsDerivIntegrand hmeas x)
    hlip hbound_int hdiff
  obtain ⟨hF'int, hFderiv⟩ := hmain
  refine ⟨hF'int, ?_⟩
  have hbiot : Work.LWP.biotSavart ω
      = fun x => (4 * Real.pi)⁻¹ • ∫ a, Work.LWP.BiotSavart.bsK ω x a := by
    funext x; exact Work.LWP.BiotSavart.biotSavart_apply ω x
  rw [hbiot]
  exact hFderiv.const_smul ((4 * Real.pi)⁻¹ : ℝ)

end Work.StabilityFar.Decay
