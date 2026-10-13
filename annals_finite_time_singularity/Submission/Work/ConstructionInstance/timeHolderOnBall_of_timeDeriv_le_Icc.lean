import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.Reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

theorem timeHolderOnBall_of_timeDeriv_le_Icc {α Λ R S : ℝ} (hS : 0 ≤ S) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hΛ : 0 ≤ Λ)
    {ω : R3 → ℝ → R3}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Set.Icc 0 S,
      HasDerivAt (fun t => ω z t) (FiniteTimeSingularity.timeDeriv ω z s) s)
    (hbd : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Set.Icc 0 S,
      ‖FiniteTimeSingularity.timeDeriv ω z s‖ ≤ Λ) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ t ∈ Set.Icc 0 S, ∀ τ ∈ Set.Icc 0 S,
        ‖ω z t - ω z τ‖ ≤ H * |t - τ| ^ α := by
  refine ⟨Λ * max S 1, mul_nonneg hΛ (le_trans zero_le_one (le_max_right _ _)), ?_⟩
  intro z hz t ht τ hτ
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) S) := convex_Icc _ _
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) S, DifferentiableAt ℝ (fun t => ω z t) x :=
    fun x hx => (hdiff z hz x hx).differentiableAt
  have hbnd : ∀ x ∈ Set.Icc (0 : ℝ) S, ‖deriv (fun t => ω z t) x‖ ≤ Λ := by
    intro x hx
    simpa only [FiniteTimeSingularity.timeDeriv] using hbd z hz x hx
  have hmvt : ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbnd hconv hτ ht
    simpa only [Real.norm_eq_abs] using h
  have hdt : |t - τ| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, hτ.1], by linarith [hτ.2, ht.1]⟩
  have hkey := Work.SolutionDelivery.Holder.self_le_max_mul_rpow (d := |t - τ|) (D := S) (α := α)
    (abs_nonneg _) hdt hα0.le hα1
  calc ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := hmvt
    _ ≤ Λ * (max S 1 * |t - τ| ^ α) := mul_le_mul_of_nonneg_left hkey hΛ
    _ = (Λ * max S 1) * |t - τ| ^ α := by ring

end Work.ConstructionInstance
