/-
# `Work.FTS.BSSwirl.CdAux` — the kernel of the derivative of the Newtonian potential

The derivative `potDeriv ω x` of the Newtonian potential is the Bochner integral of the
singular kernel `z ↦ ‖z‖⁻³ • (⟪z, ·⟫ ⊗ ω (x + z))`.  This file collects the vocabulary for the
`C¹`-statement `contDiff_one_newtonPotential`:

* `potKer z` — the scalar part `‖z‖⁻³ • ⟪z, ·⟫ : ℝ³ →L[ℝ] ℝ` of the kernel;
* `potKerBall ρ` — the same kernel cut off to the ball `B(0,ρ)`, which is *integrable* on `ℝ³`;
* the norm bound `‖potKer z‖ ≤ ‖z‖ ^ (-2 : ℝ)`, i.e. the integrable homogeneity,
* `integrable_potKerBall`, `integrableOn_potKer` — integrability of the cut-off kernel.

Nothing here is specific to the swirl problem: the kernel is that of the Newtonian potential on
`ℝ³`, whose derivative is a singular integral with kernel of homogeneity `-2` in dimension `3`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The scalar kernel of the derivative of the Newtonian potential**,
`k z = ‖z‖⁻³ • ⟪z, ·⟫ : ℝ³ →L[ℝ] ℝ`.  It is odd in `z` and of homogeneity `-2` in `z`. -/
def potKer (z : R3) : R3 →L[ℝ] ℝ :=
  (‖z‖ ^ (3 : ℕ))⁻¹ • innerSL ℝ z

/-- The kernel `potKer` cut off to the ball `B(0,ρ)`.  Unlike `potKer` itself, this is integrable
on all of `ℝ³` (the singularity `‖z‖⁻²` is integrable in dimension `3`). -/
def potKerBall (ρ : ℝ) : R3 → (R3 →L[ℝ] ℝ) :=
  (Metric.ball 0 ρ).indicator potKer

theorem potKerBall_apply_of_mem {ρ : ℝ} {z : R3} (hz : z ∈ Metric.ball 0 ρ) :
    potKerBall ρ z = potKer z :=
  Set.indicator_of_mem hz _

theorem potKerBall_apply_of_notMem {ρ : ℝ} {z : R3} (hz : z ∉ Metric.ball 0 ρ) :
    potKerBall ρ z = 0 :=
  Set.indicator_of_notMem hz _

theorem potKer_apply (z v : R3) : potKer z v = (‖z‖ ^ (3 : ℕ))⁻¹ * inner ℝ z v := by
  rw [potKer, smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- Pulling a scalar out of the first argument of `smulRight`. -/
theorem smul_smulRight (c : ℝ) (f : R3 →L[ℝ] ℝ) (v : R3) :
    (c • f).smulRight v = c • f.smulRight v := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
    smul_eq_mul]

theorem potKer_smulRight (z v : R3) :
    (potKer z).smulRight v = (‖z‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ z).smulRight v :=
  smul_smulRight _ _ _

theorem potKer_smulRight_apply (z v h : R3) :
    (potKer z).smulRight v h = ((‖z‖ ^ (3 : ℕ))⁻¹ • (innerSL ℝ z).smulRight v) h := by
  rw [potKer_smulRight, smul_apply]

/-- **The kernel is of homogeneity `-2`**: `‖k z‖ ≤ ‖z‖⁻²` (in particular it is dominated by the
integrable function `‖z‖ ^ (-2 : ℝ)`). -/
theorem potKer_norm_le (z : R3) : ‖potKer z‖ ≤ ‖z‖ ^ (-2 : ℝ) := by
  have hx : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  rw [potKer, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  have h3 : (0 : ℝ) ≤ ‖z‖ ^ (3 : ℕ) := by positivity
  rw [abs_of_nonneg (inv_nonneg.mpr h3)]
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  · have hxne : ‖z‖ ≠ 0 := ne_of_gt h
    have key : (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ = ‖z‖ ^ (-2 : ℝ) := by
      have h2 : (‖z‖ : ℝ) ^ (3 : ℕ) = ‖z‖ ^ 2 * ‖z‖ := by ring
      rw [Real.rpow_neg hx, Real.rpow_two, h2, mul_inv_rev,
        mul_comm ‖z‖⁻¹ ((‖z‖ ^ 2)⁻¹), mul_assoc, inv_mul_cancel₀ hxne, mul_one]
    rw [key]

theorem measurable_potKer : Measurable potKer := by
  rw [show potKer = fun z : R3 => (‖z‖ ^ (3 : ℕ))⁻¹ • innerSL ℝ z from rfl]
  measurability

theorem aestronglyMeasurable_potKer : AEStronglyMeasurable potKer volume :=
  measurable_potKer.aestronglyMeasurable

/-- **Integrability of the cut-off kernel.**  `potKerBall ρ` is integrable on `ℝ³` for every `ρ`:
the singularity `‖z‖⁻²` is integrable in dimension `3`, and the cut-off makes the kernel
compactly supported. -/
theorem integrable_potKerBall (ρ : ℝ) : Integrable (potKerBall ρ) volume := by
  have h1 : IntegrableOn (fun z : R3 => 1 + ‖z‖ ^ (-2 : ℝ)) (Metric.ball (0 : R3) ρ) volume :=
    Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball (-2) ρ (by norm_num)
  have h2 : Integrable ((Metric.ball (0 : R3) ρ).indicator fun z : R3 => 1 + ‖z‖ ^ (-2 : ℝ))
      volume :=
    (integrable_indicator_iff measurableSet_ball).mpr h1
  refine Integrable.mono' h2 (aestronglyMeasurable_potKer.indicator measurableSet_ball) ?_
  filter_upwards with z
  by_cases hz : z ∈ Metric.ball (0 : R3) ρ
  · simp only [potKerBall, Set.indicator_of_mem hz]
    exact le_trans (potKer_norm_le z) (le_add_of_nonneg_left zero_le_one)
  · simp only [potKerBall, Set.indicator_of_notMem hz]
    simp

/-- `potKer` is `IntegrableOn` every ball. -/
theorem integrableOn_potKer (ρ : ℝ) :
    IntegrableOn potKer (Metric.ball (0 : R3) ρ) volume := by
  change Integrable potKer (volume.restrict (Metric.ball (0 : R3) ρ))
  refine Integrable.mono'
    (g := fun z : R3 => 1 + ‖z‖ ^ (-2 : ℝ)) ?_
    (aestronglyMeasurable_potKer.mono_measure Measure.restrict_le_self) ?_
  · exact Work.CoreResiduals.BiotSavart.integrableOn_one_add_norm_rpow_ball (-2) ρ (by norm_num)
  · filter_upwards with z
    exact le_trans (potKer_norm_le z) (le_add_of_nonneg_left zero_le_one)

end

end Work.FTS.BSSwirl
