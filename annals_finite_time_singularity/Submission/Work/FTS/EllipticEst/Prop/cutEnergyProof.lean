import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyClean
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.final

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

theorem cutEnergyProof : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp α u G :=
  Work.FTS.EllipticEst.Prop.CutEnergyAux.aeCutEnergyProp_holds

end Work.FTS.EllipticEst.Prop
