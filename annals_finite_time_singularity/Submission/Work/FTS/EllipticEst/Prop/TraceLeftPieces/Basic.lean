import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Elementary facts about the weight `thEta` and the cutoff intervals

Auxiliary lemmas used by the integration-by-parts proof of the boundary product `F₀ L₀`
(`Work.FTS.EllipticEst.Prop.TraceLeftCore.prodTraceBound`).
-/

namespace Work.FTS.EllipticEst.Prop.TraceLeftCore

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### Elementary facts about the weight `thEta` -/

theorem thEta_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < thEta θ :=
  Real.rpow_pos_of_pos (Work.FTS.EllipticEst.sin_two_pos hθ) _

theorem one_le_thEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ thEta θ :=
  Work.EllipticEst.Core.one_le_thEta hθ

theorem thEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ thEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

theorem continuousOn_thEta_Ioo :
    ContinuousOn thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (Work.FTS.EllipticEst.sin_two_pos hθ).ne')

theorem sub_three : Set.Ioo (0 : ℝ) (3 * Real.pi / 8) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  fun _ hz => ⟨hz.1, by linarith [hz.2, Real.pi_pos]⟩

theorem sub_three_Iθ : Set.Ioo (0 : ℝ) (3 * Real.pi / 8) ⊆ Work.Spaces.Iθ :=
  fun _ hz => ⟨le_of_lt hz.1, le_of_lt (lt_trans hz.2 (by linarith [Real.pi_pos]))⟩

theorem three_eighths_mem : 3 * Real.pi / 8 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

/-- Interval-integrability over `(a,b)`, `a ≤ b`, follows from integrability over the open
interval. -/
theorem intervalIntegrable_of_integrableOn_Ioo {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn g (Set.Ioo a b)) : IntervalIntegrable g volume a b := by
  have h' : IntegrableOn g (Set.Ioc a b) := by
    rw [IntegrableOn,
      (MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume))).symm]
    exact h
  rwa [intervalIntegrable_iff, Set.uIoc_of_le hab]

/-- An interval integral over `(0, 3π/8)` is a set integral over `(0, 3π/8)`. -/
theorem intervalIntegral_three (g : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(3 * Real.pi / 8), g θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (3 * Real.pi / 8), g θ := by
  rw [intervalIntegral.integral_of_le (by positivity), MeasureTheory.integral_Ioc_eq_integral_Ioo]

end

end Work.FTS.EllipticEst.Prop.TraceLeftCore
