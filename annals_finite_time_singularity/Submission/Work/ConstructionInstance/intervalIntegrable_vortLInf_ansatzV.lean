import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall
import Submission.Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology NNReal

/-- **The `L^∞`-in-space norm of the vorticity of the ansatz is the closed-ball supremum of
`‖solVort‖`**: on the pre-window the vorticity of `ansatzV P = BS(solVort P · )` is `solVort P · `
(`vorticity_ansatzV`), which is supported in `B(0,R)` (`solVort_supp`) and bounded by
`M / λ̄(t)` (`solVort_bdd`). -/
theorem vortLInf_ansatzV_eq_ciSup_closedBall {α : NNReal} (P : ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ s ∈ preWindow P.T,
      Work.LWP.vortLInf (ansatzV P) s
        = ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖ := by
  intro s hs
  rw [Work.SolutionDelivery.Sup.ciSup_norm_vorticity_eq_ciSup_closedBall
    (u := ansatzV P) (R := P.R) (t := s) (M := P.M / P.lam s) P.hR ?_ ?_]
  · simp_rw [vorticity_ansatzV P hlaw s hs]
  · intro x
    rw [show FiniteTimeSingularity.vorticity (ansatzV P · s) x = solVort P x s from
      vorticity_ansatzV P hlaw s hs x]
    rw [le_div_iff₀ (P.hlam s hs), mul_comm]
    exact solVort_bdd P s hs x
  · intro x hx
    exact solVort_supp P s x (by
      intro h0
      exact hx (by
        rw [show FiniteTimeSingularity.vorticity (ansatzV P · s) x = solVort P x s from
          vorticity_ansatzV P hlaw s hs x]
        exact h0))

/-- **Continuity of the closed-ball supremum of `‖solVort‖`** on any time interval contained in
the pre-window: it is a jointly continuous family (`solVort_cont` on the core region `B(0,R+1)`)
supremised over the *compact* ball `B(0,R)`
(`Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall`). -/
theorem continuousOn_ciSup_solVort_closedBall {α : NNReal} (P : ProfileData α) {a b : ℝ}
    (hab : Set.Icc a b ⊆ preWindow P.T) :
    ContinuousOn (fun s => ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖)
      (Set.Icc a b) := by
  refine Work.SolutionDelivery.Sup.continuousOn_ciSup_closedBall
    (F := fun x s => ‖solVort P x s‖) (R := P.R) (a := a) (b := b) P.hR ?_
  refine (solVort_cont P).norm.mono ?_
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  refine ⟨?_, hab hs⟩
  have hx' : ‖x‖ ≤ P.R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  rw [Work.StabilityFar.mem_coreRegion]
  linarith

/-- **The vorticity sup-norm of the ansatz is interval integrable on `[0,t]` for `t < T`**:
on `[0,t]` it coincides with the closed-ball supremum of `‖solVort‖`, which is continuous there
(hence interval integrable). -/
theorem intervalIntegrable_vortLInf_ansatzV {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Set.Ico 0 P.T,
      IntervalIntegrable (Work.LWP.vortLInf (Work.ConstructionInstance.ansatzV P))
        MeasureTheory.volume 0 t := by
  intro t ht
  have hsub : Set.Icc 0 t ⊆ preWindow P.T :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩
  have hcont : ContinuousOn (fun s => ⨆ x ∈ Metric.closedBall 0 P.R, ‖solVort P x s‖)
      (Set.Icc 0 t) :=
    continuousOn_ciSup_solVort_closedBall P hsub
  have hcont' : ContinuousOn (Work.LWP.vortLInf (ansatzV P)) (Set.Icc 0 t) :=
    hcont.congr fun s hs =>
      vortLInf_ansatzV_eq_ciSup_closedBall P hlaw s (hsub hs)
  refine (hcont'.mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le ht.1]

end Work.ConstructionInstance
