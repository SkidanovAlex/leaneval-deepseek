/-
# `Work.CoreResiduals.BiotSavart.IntegrandDefs` — the derivative integrand of the Biot–Savart field

This file fixes the integrand appearing in the definition of the candidate derivative
`Work.CoreResiduals.BiotSavart.bsDerivCLM`,

`bsIntegrand ω x a = (crossL (ω a - ω x)).comp (kDerivCLM (x - a))`,

together with the three elementary facts about it on which the proof of the continuity of
`x ↦ bsDerivCLM ω ρ x` rests:

* `norm_bsIntegrand_le` — the pointwise bound `‖bsIntegrand ω x a‖ ≤ 4 C ‖x - a‖^{c-3}` for a
  vorticity that is `c`-Hölder with constant `C ≥ 0` (the kernel singularity at `a = x` is
  absolutely integrable because `c > 0`);
* `aestronglyMeasurable_bsIntegrand` — measurability in `a`, inherited from measurability of `ω`;
* `continuousAt_bsIntegrand` — continuity in `x` at every point `x₀ ≠ a` (the single point where
  the integrand is singular).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- The integrand of the candidate derivative `bsDerivCLM ω ρ x` of the Biot–Savart field at `x`:
`a ↦ (crossL (ω a - ω x)).comp (kDerivCLM (x - a))`. -/
noncomputable def bsIntegrand (ω : R3 → R3) (x a : R3) : R3 →L[ℝ] R3 :=
  (crossL (ω a - ω x)).comp (kDerivCLM (x - a))

@[simp]
theorem bsIntegrand_apply (ω : R3 → R3) (x a v : R3) :
    bsIntegrand ω x a v = crossL (ω a - ω x) (kDerivCLM (x - a) v) := rfl

/-- `crossL 0 = 0`. -/
theorem crossL_zero : crossL (0 : R3) = (0 : R3 →L[ℝ] R3) := by
  have h := crossL_sub (0 : R3) 0
  simpa using h

/-- **Pointwise bound for the derivative integrand.**  For a `c`-Hölder vorticity with constant
`C ≥ 0` one has `‖bsIntegrand ω x a‖ ≤ 4 C ‖x - a‖^{c-3}`; the exponent `c - 3 > -3` makes this
absolutely integrable in `a` over any bounded set. -/
theorem norm_bsIntegrand_le {ω : R3 → R3} {C c : ℝ} (hC : 0 ≤ C)
    (hhold : ∀ a b : R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (x a : R3) :
    ‖bsIntegrand ω x a‖ ≤ 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := by
  by_cases hxa : x = a
  · have hzero : bsIntegrand ω x a = 0 := by
      simp only [bsIntegrand, hxa, sub_self, crossL_zero, ContinuousLinearMap.zero_comp]
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hpos : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
    have h1 : ‖bsIntegrand ω x a‖ ≤ ‖ω a - ω x‖ * (4 / ‖x - a‖ ^ (3 : ℕ)) := by
      calc ‖bsIntegrand ω x a‖
          ≤ ‖crossL (ω a - ω x)‖ * ‖kDerivCLM (x - a)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖ω a - ω x‖ * (4 / ‖x - a‖ ^ (3 : ℕ)) := by
            exact mul_le_mul (norm_crossL_le _)
              (norm_kDerivCLM_le (x - a) ‖x - a‖ hpos le_rfl)
              (norm_nonneg _) (norm_nonneg _)
    have h2 : ‖ω a - ω x‖ ≤ C * ‖x - a‖ ^ c := by
      simpa only [norm_sub_rev] using hhold a x
    have h3 : (C * ‖x - a‖ ^ c) * (4 / ‖x - a‖ ^ (3 : ℕ))
        = 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := by
      have hsub : (‖x - a‖ : ℝ) ^ (c - 3) = (‖x - a‖ : ℝ) ^ c / (‖x - a‖ : ℝ) ^ (3 : ℝ) :=
        Real.rpow_sub hpos c 3
      rw [hsub, Real.rpow_ofNat]
      ring
    calc ‖bsIntegrand ω x a‖
        ≤ (C * ‖x - a‖ ^ c) * (4 / ‖x - a‖ ^ (3 : ℕ)) :=
          le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ = 4 * C * (‖x - a‖ : ℝ) ^ (c - 3) := h3

/-- The derivative integrand is ae-strongly-measurable in `a` whenever the vorticity is
continuous. -/
theorem aestronglyMeasurable_bsIntegrand {ω : R3 → R3} (hω : Continuous ω) (x : R3) :
    AEStronglyMeasurable (bsIntegrand ω x) volume := by
  have hω' : AEStronglyMeasurable (fun a : R3 => ω a - ω x) volume :=
    (hω.sub continuous_const).aestronglyMeasurable
  have h := aestronglyMeasurable_bsDerivIntegrand hω' x
  exact h

/-- The derivative integrand is continuous in `x` at every point `x₀ ≠ a`. -/
theorem continuousAt_bsIntegrand {ω : R3 → R3} (hω : Continuous ω) {x₀ a : R3} (ha : a ≠ x₀) :
    ContinuousAt (fun x : R3 => bsIntegrand ω x a) x₀ := by
  have h1 : ContinuousAt (fun x : R3 => crossL (ω a - ω x)) x₀ :=
    continuous_crossL.continuousAt.comp (continuousAt_const.sub hω.continuousAt)
  have hsub : ContinuousAt (fun x : R3 => x - a) x₀ := continuousAt_id.sub continuousAt_const
  have h2 : ContinuousAt (fun x : R3 => kDerivCLM (x - a)) x₀ :=
    ContinuousAt.comp (f := fun y : R3 => y - a) (x := x₀) (g := kDerivCLM)
      (continuousAt_kDerivCLM (b := x₀ - a) (show x₀ - a ≠ 0 from sub_ne_zero.mpr (Ne.symm ha)))
      hsub
  simpa only [bsIntegrand] using h1.clm_comp h2

end Work.CoreResiduals.BiotSavart
