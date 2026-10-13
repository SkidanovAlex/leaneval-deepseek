import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.FstarSmoothOfSol

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.FstarSmooth

theorem FstarInt_smoothNbhd (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (Work.FTS.EllipticEst.Cert.FstarInt α Ψ) :=
  Work.FTS.EllipticEst.Cert.FstarInt_smoothNbhdOfSol α Ψ h

end Work.FTS.EllipticEst.Cert.FstarSmooth
