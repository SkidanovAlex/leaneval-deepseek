import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.SDKey

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

theorem AsTransportSDstage {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (z : Fin 5 → R) :
    Work.MotK.kleinSecDual a b (fun k => ∑ j, Work.MotAS.asN w k j * z j)
      = Work.MotAS.kleinSecDualAS a b g z := by
  have hX : (fun k => ∑ j, Work.MotAS.asN w k j * z j)
      = (fun k => Work.MotAS.SDStage.Xk w z k) := by
    funext k
    exact Work.MotAS.SDStage.Xk_eq_asN w z k
  rw [hX]
  rw [Work.MotAS.SDStage.kleinSecDual_collect]
  exact Work.MotAS.SDStage.key a b g w z h5 hw

end Work.MotAS
