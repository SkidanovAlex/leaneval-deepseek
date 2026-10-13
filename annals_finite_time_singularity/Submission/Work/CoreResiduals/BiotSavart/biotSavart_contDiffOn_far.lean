import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.biotSavart_fderiv
import Submission.Work.StabilityFar.Decay.farField_fderiv_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped NNReal

set_option autoImplicit false

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity of the explicit far-field derivative.**  `Work.StabilityFar.Decay.norm_bsDeriv_sub_le`
bounds `‖bsDeriv ω x - bsDeriv ω y‖` by `A ‖x - y‖` on the closed far region
`{x | 2R ≤ ‖x‖}`, so `bsDeriv ω` is Lipschitz there and in particular continuous.  This is the
missing `C⁰` input of the `C¹` statement made precise in `biotSavart_contDiffOn_far`. -/
theorem continuousOn_bsDeriv_far {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hbdd : ∀ a, ‖ω a‖ ≤ M)
    (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) :
    ContinuousOn (Work.StabilityFar.Decay.bsDeriv ω) {x : Work.LWP.R3 | 2 * R ≤ ‖x‖} := by
  have hK : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ * (M * 64 / R ^ 4 * (R ^ 3 * (Real.pi * 4 / 3))) := by
    positivity
  have hLip : LipschitzOnWith
      (⟨(4 * Real.pi)⁻¹ * (M * 64 / R ^ 4 * (R ^ 3 * (Real.pi * 4 / 3))), hK⟩ : ℝ≥0)
      (Work.StabilityFar.Decay.bsDeriv ω) {x : Work.LWP.R3 | 2 * R ≤ ‖x‖} :=
    lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => by
      show ‖Work.StabilityFar.Decay.bsDeriv ω x - Work.StabilityFar.Decay.bsDeriv ω y‖
        ≤ (4 * Real.pi)⁻¹ * (M * 64 / R ^ 4 * (R ^ 3 * (Real.pi * 4 / 3))) * ‖x - y‖
      exact Work.StabilityFar.Decay.norm_bsDeriv_sub_le hR hM hbdd hs hm hx hy
  exact hLip.continuousOn

/-- **`C¹` of the Biot–Savart field in the far field.**  Outside `B(0, 2R)` there is no singularity:
`Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far` gives `HasFDerivAt (biotSavart ω) (bsDeriv ω x) x`
with the explicit derivative `bsDeriv ω x = (4π)⁻¹ • ∫ a, crossL (ω a) ∘ kDerivCLM (x - a)`, and the
derivative is continuous in `x` on that region (the dominated-convergence bound
`Work.LWP.BiotSavart.bsK_diff_le` is uniform there).  Hence `biotSavart ω` is `C¹` on `{x | 2R < ‖x‖}`. -/
theorem biotSavart_contDiffOn_far {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) :
    ContDiffOn ℝ 1 (Work.LWP.biotSavart ω) {x : Work.LWP.R3 | 2 * R < ‖x‖} := by
  have hs_open : IsOpen {x : Work.LWP.R3 | 2 * R < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  have hsub : {x : Work.LWP.R3 | 2 * R < ‖x‖} ⊆ {x : Work.LWP.R3 | 2 * R ≤ ‖x‖} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  -- `bsDeriv ω` is the derivative of `biotSavart ω` on the far region and is continuous there
  have hcont : ContinuousOn (Work.StabilityFar.Decay.bsDeriv ω)
      {x : Work.LWP.R3 | 2 * R < ‖x‖} :=
    (continuousOn_bsDeriv_far hR hM hbdd hs hm).mono hsub
  have key : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (Work.LWP.biotSavart ω)
      {x : Work.LWP.R3 | 2 * R < ‖x‖} := by
    rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs_open.uniqueDiffOn]
    refine ⟨fun h => absurd h (by simp), Work.StabilityFar.Decay.bsDeriv ω,
      contDiffOn_zero.mpr hcont, ?_⟩
    intro x hx
    exact (Work.StabilityFar.Decay.biotSavart_hasFDerivAt_far hR hM hbdd hs hm
      (le_of_lt hx)).2.hasFDerivWithinAt
  simpa using key

end Work.CoreResiduals.BiotSavart
