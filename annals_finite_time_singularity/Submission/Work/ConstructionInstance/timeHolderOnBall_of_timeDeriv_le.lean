import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.SolutionDelivery.Holder.timeHolderOnBall_of_isContDiffHolderOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

/-- **A time-Lipschitz bound for the vorticity from a bound on `∂ₜω`.**

If, on the ball of radius `R`, every time slice `t ↦ ω z t` is differentiable on the window
`window S = [-1, S+1]` with derivative `∂ₜω z`, and `‖∂ₜω z t‖ ≤ Λ` there, then `ω` is
`α`-Hölder in time on that ball and window for every `0 < α ≤ 1`.

The proof is the mean value theorem (bounded derivative ⟹ `Λ`-Lipschitz in time, on the convex
window) followed by the elementary `|t-τ| ≤ max(S+2) 1 · |t-τ|^α` on a set of diameter `S+2`
(`Work.SolutionDelivery.Holder.self_le_max_mul_rpow`); the constant is
`H = Λ · max (S+2) 1`. -/
theorem timeHolderOnBall_of_timeDeriv_le {α Λ R S : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hΛ : 0 ≤ Λ)
    {ω : Work.ConstructionInstance.R3 → ℝ → Work.ConstructionInstance.R3}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) R,
      ∀ s ∈ Work.StabilityFar.window S,
        HasDerivAt (fun t => ω z t) (FiniteTimeSingularity.timeDeriv ω z s) s)
    (hbd : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) R,
      ∀ s ∈ Work.StabilityFar.window S, ‖FiniteTimeSingularity.timeDeriv ω z s‖ ≤ Λ) :
    ∃ H : ℝ, 0 ≤ H ∧ Work.StabilityFar.TimeHolderOnBall α ω R S H := by
  refine ⟨Λ * max (S + 2) 1, mul_nonneg hΛ (le_trans (by norm_num) (le_max_right _ _)), ?_⟩
  intro z hz t ht τ hτ
  have hconv : Convex ℝ (Work.StabilityFar.window S) := by
    rw [Work.StabilityFar.window]; exact convex_Icc _ _
  have hderiv : ∀ x ∈ Work.StabilityFar.window S, DifferentiableAt ℝ (fun t => ω z t) x :=
    fun x hx => (hdiff z hz x hx).differentiableAt
  have hbnd : ∀ x ∈ Work.StabilityFar.window S, ‖deriv (fun t => ω z t) x‖ ≤ Λ := by
    intro x hx
    simpa only [FiniteTimeSingularity.timeDeriv] using hbd z hz x hx
  have hmvt : ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbnd hconv hτ ht
    simpa only [Real.norm_eq_abs] using h
  have hdt : |t - τ| ≤ S + 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, hτ.1], by linarith [hτ.2, ht.1]⟩
  have hkey := Work.SolutionDelivery.Holder.self_le_max_mul_rpow (d := |t - τ|) (D := S + 2)
    (α := α) (abs_nonneg _) hdt hα0.le hα1
  calc ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := hmvt
    _ ≤ Λ * (max (S + 2) 1 * |t - τ| ^ α) := mul_le_mul_of_nonneg_left hkey hΛ
    _ = (Λ * max (S + 2) 1) * |t - τ| ^ α := by ring

end Work.ConstructionInstance
