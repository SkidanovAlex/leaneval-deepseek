import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.solVort_integrable
import Submission.Work.ConstructionInstance.solVort_isBoundedFun
import Submission.Work.LWP.BiotSavart
import Submission.Work.LWP.Inputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem vorticity_biotSavart_solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T, ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.vorticity
          (Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t)) x
        = Work.ConstructionInstance.solVort P x t := by
  intro t ht x
  exact ((hlaw (fun y => solVort P y t) (solVort_integrable P t ht)
    (solVort_isBoundedFun P t ht) (fun x => congrFun (solVort_div P t ht) x)).1 x)

end Work.ConstructionInstance
