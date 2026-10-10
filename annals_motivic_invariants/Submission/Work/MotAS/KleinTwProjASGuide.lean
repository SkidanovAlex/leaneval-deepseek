import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASTransportR0
import Submission.Work.MotAS.ASTransportR1
import Submission.Work.MotAS.ASTransportR2
import Submission.Work.MotAS.ASTransportR3
import Submission.Work.MotAS.ASTransportR4
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The projective (ratio) form of the AS link identity I1^AS

`R^AS ∘ P^AS` is a scalar multiple of the identity, in cross-multiplied form:
`kleinRAS (kleinPAS y) i * y j = kleinRAS (kleinPAS y) j * y i`.

(This is the same statement as `Work.MotAS.ASI1Ratio`, restated at a fresh path; it is the only
part of I1^AS that is *cheap*, and it is what the chart-isomorphism proof consumes — the exact
scalar `kleinSecAS y` is the subject of `Work.MotAS.KleinTwScalarAS`.)

## Suggested route (cheap: transports + cancellation, no big `ring`)

Let `S := AdjoinRoot (Polynomial.X^5 - Polynomial.X - Polynomial.C g)` over `R`, `w := AdjoinRoot.root _`
(so `w^5 = w + g` and `5 = 0` in `S`), and `ξ := fun i => ∑ j, asM w i j * y j`.

* `asTransportP` gives `kleinP a b ξ = (asN w).mulVec (kleinPAS a b g y)`;
* `Work.MotK.KleinIdents.kleinR_kleinP` gives
  `kleinR a b (kleinP a b ξ) = fun i => kleinSec a b ξ * ξ i`;
* `asTransportR` gives `kleinR a b ((asN w).mulVec (kleinPAS a b g y))
  = (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y))`;
* hence `(asM w).mulVec (kleinRAS a b g (kleinPAS a b g y)) = fun i => kleinSec a b ξ * ξ i`,
  and since `asM w` is invertible (`asM_mulVec_injective`, `isUnit_288`, using `5 = 0`;
  see `Submission.Work.MotAS.ASMatrix`) we get
  `kleinRAS a b g (kleinPAS a b g y) = fun i => kleinSec a b ξ * y i` in `S`;
* multiply components `i` and `j` by `y j` and `y i` and commute;
* descend to `R` with `AdjoinRoot.of.injective_of_monic_of_degree_pos`.

The transports and `asM_mulVec_injective` are already proved in the workspace.
-/

-- (guidance only; the theorem statement lives at `Work/MotAS/KleinTwProjAS`)
