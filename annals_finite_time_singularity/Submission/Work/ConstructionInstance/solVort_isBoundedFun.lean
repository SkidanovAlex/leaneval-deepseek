import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.Stability.OmegaCutHolder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The `L^∞` box `λ̄(t)·‖ω(x,t)‖ ≤ M` of `solVort_bdd` gives the pointwise norm bound
`‖ω(x,t)‖ ≤ M/λ̄(t)` used below. -/
theorem solVort_norm_le {α : NNReal} (P : ProfileData α) {t : ℝ}
    (ht : t ∈ preWindow P.T) (x : R3) :
    ‖solVort P x t‖ ≤ P.M / P.lam t := by
  have hpos : 0 < P.lam t := P.hlam t ht
  rw [le_div_iff₀ hpos, mul_comm]
  exact solVort_bdd P t ht x

theorem solVort_isBoundedFun {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      IsBoundedFun (fun x => Work.ConstructionInstance.solVort P x t) := by
  intro t ht
  exact Work.Stability.isBoundedFun_of_forall_norm_le
    (f := fun x => solVort P x t) (C := P.M / P.lam t) (fun x => solVort_norm_le P ht x)

end Work.ConstructionInstance
