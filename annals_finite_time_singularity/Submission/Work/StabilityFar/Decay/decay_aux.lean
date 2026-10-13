/-
# `Work.StabilityFar.Decay.decay_aux` — regularity boilerplate for the far-field
second-derivative estimate

The differentiability of `biotSavart ω` in the far field is obtained by differentiating under the
Bochner integral (`hasFDerivAt_integral_of_dominated_loc_of_lip`).  That requires

* continuity of `crossL` (the cross product as a map of the left argument) so that
  `a ↦ crossL (ω a)` is ae-strongly-measurable whenever `ω` is;
* measurability of `a ↦ kDerivCLM (x - a)` (the kernel derivative except at the single
  singular point `a = x`);
* continuity of the composition of continuous linear maps, so that the derivative integrand
  `a ↦ crossL (ω a) ∘ kDerivCLM (x - a)` is ae-strongly-measurable.

These are the content of this file.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.FarField
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.norm_crossL_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.StabilityFar.Decay

open Work.LWP

theorem crossL_sub (u u' : R3) : crossL (u - u') = crossL u - crossL u' := by
  ext v
  simp only [crossL_apply, sub_apply, WithLp.ofLp_sub, map_sub, LinearMap.sub_apply,
    Pi.sub_apply, WithLp.toLp_sub]

/-- `crossL` is `1`-Lipschitz, hence continuous, as a map into the space of continuous linear maps:
`‖u × · - u' × ·‖ ≤ ‖u - u'‖`. -/
theorem lipschitzWith_crossL : LipschitzWith 1 crossL := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u u'
  rw [dist_eq_norm, dist_eq_norm, ← crossL_sub]
  simpa using norm_crossL_le (u - u')

theorem continuous_crossL : Continuous crossL :=
  lipschitzWith_crossL.continuous

/-- Continuity of `b ↦ ⟪b,·⟫ ⊗ b` at a nonzero point. -/
theorem continuousAt_smulRight (b : R3) :
    ContinuousAt (fun b : R3 => (innerSL ℝ b).smulRight b) b := by
  have heq : (fun b : R3 => (innerSL ℝ b).smulRight b)
      = fun b => ContinuousLinearMap.smulRightL ℝ R3 R3 (innerSL ℝ b) b := by
    funext b; ext v
    simp [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply]
  rw [heq]
  have hf : Continuous (fun b : R3 => ContinuousLinearMap.smulRightL ℝ R3 R3 (innerSL ℝ b)) :=
    (ContinuousLinearMap.continuous (ContinuousLinearMap.smulRightL ℝ R3 R3)).comp (by fun_prop)
  exact (hf.clm_apply continuous_id).continuousAt

/-- `kDerivCLM` is continuous away from the origin. -/
theorem continuousAt_kDerivCLM {b : R3} (hb : b ≠ 0) : ContinuousAt kDerivCLM b := by
  have h1 : ContinuousAt (fun b : R3 => (‖b‖ ^ (3 : ℕ))⁻¹) b := by
    apply ContinuousAt.inv₀ (by fun_prop); simp [hb]
  have h2 : ContinuousAt (fun b : R3 => (3 * (‖b‖ ^ (5 : ℕ))⁻¹)) b := by
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.inv₀ (by fun_prop); simp [hb]
  have h3 := continuousAt_smulRight b
  have hA : ContinuousAt
      (fun b : R3 => (‖b‖ ^ (3 : ℕ))⁻¹ • (ContinuousLinearMap.id ℝ R3 : R3 →L[ℝ] R3)) b :=
    h1.smul continuousAt_const
  have hB : ContinuousAt (fun b : R3 => (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • (innerSL ℝ b).smulRight b) b :=
    h2.smul h3
  have hsub : ContinuousAt
      ((fun b : R3 => (‖b‖ ^ (3 : ℕ))⁻¹ • (ContinuousLinearMap.id ℝ R3 : R3 →L[ℝ] R3))
        - (fun b : R3 => (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • (innerSL ℝ b).smulRight b)) b := hA.sub hB
  have heq : kDerivCLM
      = (fun b : R3 => (‖b‖ ^ (3 : ℕ))⁻¹ • (ContinuousLinearMap.id ℝ R3 : R3 →L[ℝ] R3))
        - (fun b : R3 => (3 * (‖b‖ ^ (5 : ℕ))⁻¹) • (innerSL ℝ b).smulRight b) := by
    funext b; simp only [kDerivCLM, Pi.sub_apply]
  rwa [heq]

/-- `a ↦ kDerivCLM (x - a)` is Borel measurable (it is continuous off the single point `x`). -/
theorem measurable_kDerivCLM_sub (x : R3) : Measurable (fun a : R3 => kDerivCLM (x - a)) := by
  apply measurable_of_continuousOn_compl_singleton x
  intro a ha
  have ha' : a ≠ x := by simpa using ha
  exact (continuousAt_kDerivCLM (sub_ne_zero.mpr (Ne.symm ha'))).comp
    (continuousAt_const.sub continuousAt_id) |>.continuousWithinAt

/-- Composition of continuous linear maps is continuous, as a map on the product. -/
theorem continuous_compL :
    Continuous (fun p : (R3 →L[ℝ] R3) × (R3 →L[ℝ] R3) => p.1.comp p.2) :=
  ContinuousLinearMap.continuous₂ (ContinuousLinearMap.compL ℝ R3 R3 R3)

/-- The derivative integrand of the Biot–Savart field in the far field is ae-strongly-measurable
whenever the vorticity is. -/
theorem aestronglyMeasurable_bsDerivIntegrand {ω : R3 → R3}
    (hω : AEStronglyMeasurable ω volume) (x : R3) :
    AEStronglyMeasurable (fun a : R3 => (crossL (ω a)).comp (kDerivCLM (x - a))) volume := by
  have h1 : AEStronglyMeasurable (fun a : R3 => crossL (ω a)) volume :=
    continuous_crossL.comp_aestronglyMeasurable hω
  have h2 : AEStronglyMeasurable (fun a : R3 => kDerivCLM (x - a)) volume :=
    (measurable_kDerivCLM_sub x).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun a : R3 => (crossL (ω a), kDerivCLM (x - a))) volume :=
    h1.prodMk h2
  exact continuous_compL.comp_aestronglyMeasurable h3

end Work.StabilityFar.Decay
