import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.levelHom
import Submission.Work.Q44Geom.isSolIff

/-!
# Level forms for the quartic `f = ⟨c, ν_{4,4}⟩`

This module collects the properties of the level forms `levelForm w b₁ b₂ f α` (the
coefficients of `u^α` in `f(Σ p_a w_a + u₀ b₁ + u₁ b₂)`), all proved in the imported
modules:

* `evalSigma` : evaluating `sigma` at `(p,u)` is evaluating `f` at `substPoint w b₁ b₂ p u`;
* `levelHom`   : the level forms are homogeneous of degree `4 - |α|`;
* `isSolIff`   : for homogeneous `f` of degree `4` vanishing on `ℓ`, the vanishing of `f` on
  `ℓ + ℚ (Σ p_a w_a)` is equivalent to the vanishing of the ten level forms of degree `≤ 3`
  at `p`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

end Work.Q44Geom
