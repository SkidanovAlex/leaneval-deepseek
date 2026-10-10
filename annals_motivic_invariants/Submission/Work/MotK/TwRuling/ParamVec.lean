import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.MotK.TwRuling

/-- **The parametrisation of the target ruling divisor in characteristic two.**

`paramVec K D h` is the point with `z 0 = 0`, `z 1 = t`, `z 2 = y 2 + (b/a) h y 4 t`,
`z 3 = (b/a) y 1 + h y 3 t`, `z 4 = 1`, where `y = sdY K D h` are the twisted Klein coordinates
(so `y 0 = 1` and `kleinTwP a b h y = 0`) and `t = RatFunc.X`.  Numerically (exact arithmetic over
`F_64`, seven triples `(a,b,h)`) the map `t ↦ paramVec` lands in the surface `{sdualT = 0}` and
`kleinTwR a b h (paramVec K D h) ∝ y`; this is the characteristic-two replacement for the
degenerate polar presentation `Work.MotK.TGen.sdPhi`. -/
noncomputable def paramVec (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Fin 5 → Work.MotK.TGen.sdA K D h :=
  ![(0 : Work.MotK.TGen.sdA K D h),
    (RatFunc.X : Work.MotK.TGen.sdA K D h),
    Work.MotK.TGen.sdY K D h 2
      + (algebraMap K (Work.MotK.TGen.sdA K D h) D.b
          / algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        * algebraMap K (Work.MotK.TGen.sdA K D h) h * Work.MotK.TGen.sdY K D h 4
        * (RatFunc.X : Work.MotK.TGen.sdA K D h),
    (algebraMap K (Work.MotK.TGen.sdA K D h) D.b
        / algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      * Work.MotK.TGen.sdY K D h 1
      + algebraMap K (Work.MotK.TGen.sdA K D h) h * Work.MotK.TGen.sdY K D h 3
        * (RatFunc.X : Work.MotK.TGen.sdA K D h),
    1]

/-- The image of the parametrisation as a `K`-subalgebra of `sdA K D h`: the subalgebra generated
by the three coordinate functions `t`, `y 2 + (b/a) h y 4 t`, `(b/a) y 1 + h y 3 t`. -/
noncomputable def paramR (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Subalgebra K (Work.MotK.TGen.sdA K D h) :=
  Algebra.adjoin K (Set.range (fun j : Fin 3 =>
    ![paramVec K D h 1, paramVec K D h 2, paramVec K D h 3] j))

end Work.MotK.TwRuling
