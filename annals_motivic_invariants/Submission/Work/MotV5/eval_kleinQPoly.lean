import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem eval_kleinQPoly {R : Type*} [CommRing R] (a b : R) (P : Polynomial R) (t : R) :
    (Work.MotV5.kleinQPoly a b P).eval t =
      Work.MotK.kleinP0 a b (fun j : Fin 5 => P.eval (t + ((j:ℕ) : R))) := by
  simp [Work.MotV5.kleinQPoly, Work.MotK.kleinP0]

end Work.MotV5
