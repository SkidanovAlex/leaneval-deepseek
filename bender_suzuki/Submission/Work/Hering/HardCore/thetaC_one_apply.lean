import Mathlib
import Submission.Work.Hering.AppVIII.CTwoStepDefs
import Submission.Work.Hering.AppVIII.frobPowOfFourth

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

theorem thetaC_one_apply (x : GaloisField 2 3) : Work.Hering.AppVIII.thetaC 1 x = x ^ 2 := by
  -- `thetaC 1 = (frobeniusEquiv (KC 1) 2) ^ 1` and `KC 1 = GaloisField 2 3`.
  show ((frobeniusEquiv (GaloisField 2 3) 2) ^ 1) x = x ^ 2
  rw [pow_one]
  -- `frobeniusEquiv_pow_apply 3 1 x : (frobeniusEquiv _ 2 ^ 1) x = x ^ (2 ^ 1) = x ^ 2`.
  exact Work.Hering.AppVIII.frobeniusEquiv_pow_apply 3 1 x

end Work.Hering.HardCore
