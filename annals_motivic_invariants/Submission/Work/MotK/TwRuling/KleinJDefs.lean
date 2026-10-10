import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The discrete invariants `c₄`, `D` of the Hesse (Klein) family

`kleinC4 a b` and `kleinDisc a b` are Fisher's `c₄`-invariant and discriminant of the Klein
(Pfaffian) quintic `C_{a,b} = V(p_0,…,p_4)`: the Jacobian of `C_{a,b}` is
`y² = x³ - 27 c₄ x - 54 c₆`, and its `j`-invariant is `kleinC4³ / kleinDisc⁵`.

At `(a,b) = (1,1)`: `kleinC4 = 496`, `kleinDisc = -11`, so `j = 496³/(-11)⁵ = -122023936/161051`,
the `j`-invariant of the Tate normal form `E₁₁ : y² - 10xy - 11y = x³ - 11x²` (the `b = 11` member),
which is the standard Klein datum with parameters `(1,1)`.

The identity `kleinC4 a b ^ 3 = j · kleinDisc a b ^ 5` is an *integer* polynomial identity in
`a, b`, so it holds in every commutative ring.
-/

set_option autoImplicit false

namespace Work.MotK.TwRuling

/-- Fisher's `c₄`-invariant `a²⁰ + 228a¹⁵b⁵ + 494a¹⁰b¹⁰ - 228a⁵b¹⁵ + b²⁰` of the Klein quintic. -/
def kleinC4 {K : Type*} [CommRing K] (a b : K) : K :=
  a ^ 20 + 228 * a ^ 15 * b ^ 5 + 494 * a ^ 10 * b ^ 10 - 228 * a ^ 5 * b ^ 15 + b ^ 20

/-- Fisher's discriminant `a·b·(a¹⁰ - 11a⁵b⁵ - b¹⁰)` of the Klein quintic. -/
def kleinDisc {K : Type*} [CommRing K] (a b : K) : K :=
  a * b * (a ^ 10 - 11 * a ^ 5 * b ^ 5 - b ^ 10)

end Work.MotK.TwRuling
