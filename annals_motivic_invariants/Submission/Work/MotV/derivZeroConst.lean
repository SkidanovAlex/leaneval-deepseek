import Mathlib
import Submission.Work.MotV.DerivZeroDefs
import Submission.Work.MotV.polyDerivZero
import Submission.Work.MotV.genYNotMemBaseField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

namespace Work.MotV

noncomputable section

/-- The derivation `D` on `N(E)` with `D x = 2y + a₁x + a₃`, `D y = 3x² + 2a₂x + a₄ - a₁y`
(the derivation dual to the invariant differential) has kernel the constants.

The proof is `derivZeroConst_aux` (in `DerivZeroDefs`), applied to: the normal form
`N(E) = N(x) + N(x)·w` with `w = invDP E = 2y + a₁x + a₃` (`invDP_normalForm`), the fact that a
rational function of `x` with vanishing derivative is constant (`polyDerivZero`), the two facts
`B'(x) ≠ 0` and `deg B = 3` for `B = bPoly E = (a₁X+a₃)² + 4(X³+a₂X²+a₄X+a₆)`
(`bPoly_derivative_ne_zero`, `bPoly_natDegree`), and `y ∉ N(x)` (`genYNotMemBaseField`). -/
theorem derivZeroConst {N : Type*} [Field N] [CharZero N] (E : WeierstrassCurve N)
    [E.IsElliptic]
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) :
    ∀ f : Work.MotC2.Func E, D f = 0 → ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f :=
  derivZeroConst_aux (N := N) E D hDx hDy
    (fun f => invDP_normalForm E (by norm_num) f)
    (polyDerivZero N E)
    (bPoly_derivative_ne_zero E)
    (bPoly_natDegree E)
    (genYNotMemBaseField N E)

end

end Work.MotV
