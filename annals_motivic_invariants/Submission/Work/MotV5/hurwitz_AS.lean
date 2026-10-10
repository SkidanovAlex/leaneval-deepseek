import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.haMain

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem hurwitz_AS {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N) [E.IsElliptic] (f : Polynomial N) (hf2 : 2 ≤ f.natDegree)
    (hf5 : ¬ 5 ∣ f.natDegree) (r : WeierstrassCurve.Affine.FunctionField E)
    (hr : ∀ v : Valuation (WeierstrassCurve.Affine.FunctionField E) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn N v → 1 < v r →
      ∃ u, v (Polynomial.aeval r f - (u ^ 5 - u)) ≤ 1) :
    ∃ c : N, algebraMap N _ c = r :=
  hurwitz_AS_main E f hf2 hf5 r hr

end Work.MotV5
