import Mathlib
import Submission.Work.Pi6.EFACTS.MSSSetup
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Stems.CollapseDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EFACTS

/-- **The sphere model `SphModel 3 = OnePoint ℝ³` is simply connected**, at *every* base point
`y` (the statement is base-point independent: it is obtained by transporting the connectivity of
the round sphere `S³` across the one-point-compactification homeomorphism
`Work.Stems.onePointSphereHomeo 3 : SphModel 3 ≃ₜ S³`).

This is the connectivity input that lets the Wang-sequence machinery of area EFACTS be used over
the model `SphModel 3`, and it is what `SimplyConn`-hypotheses downstream ask for. -/
theorem sphModelSimplyConn (y : Work.StemsB.SphModel 3) :
    Work.PiS.SimplyConn (Work.StemsB.SphModel 3) y := by
  refine ⟨?_, ?_⟩
  · -- `π₀`: transport `Subsingleton (π₀ S³)` across `onePointSphereHomeo 3`
    exact Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
      (Work.Stems.onePointSphereHomeo 3) rfl 0
      (Work.Stems.sphereConnectivity 3 0 (by norm_num) ((Work.Stems.onePointSphereHomeo 3) y))
  · -- `π₁`: same in degree `1` (`S³` is `2`-connected)
    exact Work.Stems.subsingleton_homotopyGroup_fin_of_homeomorph
      (Work.Stems.onePointSphereHomeo 3) rfl 1
      (Work.Stems.sphereConnectivity 3 1 (by norm_num) ((Work.Stems.onePointSphereHomeo 3) y))

end Work.Pi6.EFACTS
