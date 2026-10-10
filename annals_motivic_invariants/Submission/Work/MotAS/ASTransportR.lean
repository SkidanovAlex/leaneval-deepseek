import Submission.Work.MotAS.ASTransportR0
import Submission.Work.MotAS.ASTransportR1
import Submission.Work.MotAS.ASTransportR2
import Submission.Work.MotAS.ASTransportR3
import Submission.Work.MotAS.ASTransportR4

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Bundled transport of the inverse quadro-cubic map. -/

set_option autoImplicit false
namespace Work.MotAS
variable {R : Type*} [CommRing R]

/-- Bundled transport of the inverse map: `R(asN w · ẑ) = asM w · R^AS(ẑ)`. -/
theorem asTransportR (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (z : Fin 5 → R) :
    Work.MotK.kleinR a b (fun k => ∑ j, asN w k j * z j) = (asM w).mulVec (kleinRAS a b g z) := by
  funext i
  fin_cases i
  · exact asTransportR0 a b g w h5 hw z
  · exact asTransportR1 a b g w h5 hw z
  · exact asTransportR2 a b g w h5 hw z
  · exact asTransportR3 a b g w h5 hw z
  · exact asTransportR4 a b g w h5 hw z

end Work.MotAS
