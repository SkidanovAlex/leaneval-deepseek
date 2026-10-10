import Mathlib
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotV5.SpreadLoc.isLocalization_spreadMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- `Work.MotA.spreadMap 𝕜 n : 𝕜[t,x₁,…,xₙ] →ₐ[𝕜] K[x₁,…,xₙ]` (`K = RatFunc 𝕜`) is the
localization at the submonoid `M := (nonZeroDivisors 𝕜[t]).map (tPoly 𝕜 n)` of "vertical"
elements, for the `𝕜[t,x]`-algebra structure on `K[x]` given by `RingHom.toAlgebra`.

This is the node statement of the `MotV5` census; its proof lives in
`Submission/Work/MotV5/SpreadLoc/isLocalization_spreadMap.lean` (namespace `Work.MotV5.SpreadLoc`),
which is the live version of this declaration (the same statement has three copies in the
workspace, all with the same proof). -/
theorem isLocalization_spreadMap (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    letI : Algebra (MvPolynomial (Fin (n+1)) 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
      RingHom.toAlgebra (Work.MotA.spreadMap 𝕜 n).toRingHom
    IsLocalization ((nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 n))
      (MvPolynomial (Fin n) (RatFunc 𝕜)) :=
  Work.MotV5.SpreadLoc.isLocalization_spreadMap 𝕜 n

end Work.MotV5
