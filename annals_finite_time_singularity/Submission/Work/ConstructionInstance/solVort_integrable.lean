import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Reduced

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology

namespace Work.ConstructionInstance

theorem solVort_integrable {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      MeasureTheory.Integrable (fun x => Work.ConstructionInstance.solVort P x t) := by
  intro t ht
  have hsmeas : MeasurableSet (Metric.closedBall (0 : R3) (P.R + 1)) :=
    isClosed_closedBall.measurableSet
  -- the slice of the vorticity is continuous on the ball
  have hcont : ContinuousOn (fun x : R3 => solVort P x t)
      (Metric.closedBall (0 : R3) (P.R + 1)) := by
    have hmaps : Set.MapsTo (fun x : R3 => (x, t)) (Metric.closedBall (0 : R3) (P.R + 1))
        (Work.StabilityFar.coreRegion (P.R + 1) ×ˢ preWindow P.T) := by
      intro x hx
      refine ⟨?_, ht⟩
      show ‖x‖ ≤ P.R + 1
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact hx
    have hc : Continuous (fun x : R3 => (x, t)) := continuous_id.prodMk continuous_const
    exact (solVort_cont P).comp hc.continuousOn hmaps
  have haes : AEStronglyMeasurable (fun x : R3 => solVort P x t)
      (volume.restrict (Metric.closedBall (0 : R3) (P.R + 1))) :=
    ContinuousOn.aestronglyMeasurable hcont hsmeas
  have hfin : volume (Metric.closedBall (0 : R3) (P.R + 1)) < ⊤ := measure_closedBall_lt_top
  have hbound : ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : R3) (P.R + 1))),
      ‖solVort P x t‖ ≤ P.M / P.lam t := by
    refine Eventually.of_forall (fun x => ?_)
    rw [le_div_iff₀ (P.hlam t ht), mul_comm]
    exact solVort_bdd P t ht x
  have hIntOn : IntegrableOn (fun x : R3 => solVort P x t)
      (Metric.closedBall (0 : R3) (P.R + 1)) volume :=
    IntegrableOn.of_bound hfin haes (P.M / P.lam t) hbound
  have hsupp : Function.support (fun x : R3 => solVort P x t) ⊆
      Metric.closedBall (0 : R3) (P.R + 1) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact closedBall_subset_closedBall (by linarith) (solVort_supp P t x hx)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

end Work.ConstructionInstance
