import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.asW0Defs` — explicit coefficient data for the nonvanishing of `asRuleQW · 0`

The ruling coordinate `W 0` (`W = asRuleQW a b g c RatFunc.X`) is `A(c) + t * B(c)` with
`B = asPolarP a b g c (asTanQ a b c 2) 0` a quadratic form in the curve coordinates `c`, and `t`
transcendental; so it suffices to prove `B ≠ 0` on the twisted Klein curve.  By the
multiplication-map machinery (`Work.MotK.TwRuling.SdWfour.Phi`) the quadratic relations among the
products `κ_i κ_j` of the five AS coordinates are spanned by the coefficient vectors of the five
AS Pfaffians `kleinPAS k`, and `B ≠ 0` follows from an explicit linear functional (`psiAS`) that
kills the five Pfaffian vectors but not the coefficient vector `cB` of `B`.

This file only fixes the three explicit vectors (`cPASmat`, `cB`, `psiAS`), in the pair indexing
`(k,0) ↦ {2k,2k}`, `(k,1) ↦ {2k+2,2k+3}`, `(k,2) ↦ {2k+1,2k+4}` of `SdWfour.pfA`/`pfB`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- The coefficient matrix of the `k`-th AS Pfaffian `kleinPAS k`: entry `(i,s)` is the
coefficient of `y_{pfA (i,s)} * y_{pfB (i,s)}` in `kleinPAS k`. -/
def cPASmat (a b g : R) : Fin 5 → Matrix (Fin 5) (Fin 3) R :=
  ![  !![    a^(2:ℕ) - a * b - b^(2:ℕ), 2 * a^(2:ℕ) * g - 2 * a * b * g - 2 * b^(2:ℕ) * g, 2 * a^(2:ℕ) * g - 2 * a * b * g - 2 * b^(2:ℕ) * g;
    a^(2:ℕ) - b^(2:ℕ), 2 * a^(2:ℕ) - 2 * b^(2:ℕ), -2 * a^(2:ℕ) + 2 * b^(2:ℕ);
    a^(2:ℕ) - b^(2:ℕ), 0, 0;
    a^(2:ℕ) + b^(2:ℕ), a^(2:ℕ) * g + b^(2:ℕ) * g, -2 * a^(2:ℕ) - 2 * b^(2:ℕ);
    a^(2:ℕ) + b^(2:ℕ), 0, -2 * a^(2:ℕ) - 2 * b^(2:ℕ)],
  !![    0, -a^(2:ℕ) - 2 * a * b + b^(2:ℕ), a^(2:ℕ) - 2 * a * b - b^(2:ℕ);
    0, 0, 0;
    -a^(2:ℕ) * g - b^(2:ℕ) * g, 2 * a^(2:ℕ) + 2 * b^(2:ℕ), -a^(2:ℕ) - b^(2:ℕ);
    0, -2 * a^(2:ℕ) - 2 * b^(2:ℕ), 0;
    a^(2:ℕ) * g - a * b * g - b^(2:ℕ) * g, 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ), 2 * a^(2:ℕ) * g - 2 * a * b * g - 2 * b^(2:ℕ) * g],
  !![    0, 0, 0;
    2 * a^(2:ℕ) + 2 * b^(2:ℕ), -2 * a^(2:ℕ) - 2 * b^(2:ℕ), 0;
    -2 * a^(2:ℕ) - 2 * b^(2:ℕ), 0, 0;
    a^(2:ℕ) - a * b - b^(2:ℕ), 2 * a^(2:ℕ) * g - 2 * a * b * g - 2 * b^(2:ℕ) * g, 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ);
    -a^(2:ℕ) - a * b + b^(2:ℕ), 0, -2 * a * b],
  !![    0, -a^(2:ℕ) - b^(2:ℕ), a^(2:ℕ) + b^(2:ℕ);
    0, 0, 0;
    a^(2:ℕ) * g - a * b * g - b^(2:ℕ) * g, 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ), 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ);
    0, -2 * a^(2:ℕ) - 2 * a * b + 2 * b^(2:ℕ), 0;
    0, 0, 0],
  !![    0, 0, 0;
    a^(2:ℕ) - a * b - b^(2:ℕ), 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ), 2 * a^(2:ℕ) - 2 * a * b - 2 * b^(2:ℕ);
    2 * a^(2:ℕ) - a * b - 2 * b^(2:ℕ), 0, 0;
    0, 0, 0;
    -2 * a^(2:ℕ) - 2 * b^(2:ℕ), 0, 2 * a^(2:ℕ) + 2 * b^(2:ℕ)]]

/-- The coefficient vector of `kleinPAS k`, as a function on the fifteen unordered pairs. -/
def cPAS (a b g : R) (k : Fin 5) : Fin 5 × Fin 3 → R :=
  fun q => cPASmat a b g k q.1 q.2

/-- The coefficient vector of the quadratic form `B = asPolarP a b g c (asTanQ a b c 2) 0` in the
fifteen pair monomials. -/
def cB (a b g : R) : Fin 5 × Fin 3 → R :=
  fun q => (!![    -4 * a^(4:ℕ) + 4 * a^(3:ℕ) * b + 4 * a * b^(3:ℕ) + 4 * b^(4:ℕ), 2 * a^(4:ℕ) * g - 2 * a^(3:ℕ) * b * g - 2 * a * b^(3:ℕ) * g - 2 * b^(4:ℕ) * g, -4 * a^(4:ℕ) * g + 4 * a^(3:ℕ) * b * g + 4 * a * b^(3:ℕ) * g + 4 * b^(4:ℕ) * g;
    8 * a^(4:ℕ) - 4 * a^(3:ℕ) * b - 4 * a * b^(3:ℕ) - 8 * b^(4:ℕ), -16 * a^(4:ℕ) + 8 * a^(3:ℕ) * b + 8 * a * b^(3:ℕ) + 16 * b^(4:ℕ), 0;
    -12 * a^(4:ℕ) + 4 * a^(3:ℕ) * b + 4 * a * b^(3:ℕ) + 12 * b^(4:ℕ), -4 * a^(4:ℕ) * g + 8 * a^(3:ℕ) * b * g + 4 * a^(2:ℕ) * b^(2:ℕ) * g - 8 * a * b^(3:ℕ) * g - 4 * b^(4:ℕ) * g, 4 * a^(4:ℕ) * g - 8 * a^(3:ℕ) * b * g - 4 * a^(2:ℕ) * b^(2:ℕ) * g + 8 * a * b^(3:ℕ) * g + 4 * b^(4:ℕ) * g;
    0, 6 * a^(4:ℕ) * g - 12 * a^(3:ℕ) * b * g - 16 * a^(2:ℕ) * b^(2:ℕ) * g + 12 * a * b^(3:ℕ) * g + 6 * b^(4:ℕ) * g, -4 * a^(4:ℕ) - 8 * a^(2:ℕ) * b^(2:ℕ) - 4 * b^(4:ℕ);
    0, 0, 4 * a^(4:ℕ) - 8 * a^(2:ℕ) * b^(2:ℕ) + 4 * b^(4:ℕ)] : Matrix (Fin 5) (Fin 3) R) q.1 q.2

/-- The certificate linear functional: it annihilates the five Pfaffian coefficient vectors and
takes the value `-2 a² b (a² - ab - b²)` on `cB`. -/
def psiAS (a b : R) : Fin 5 × Fin 3 → R :=
  fun q => (!![    2 * a - b, 0, 0;
    -2 * a + 2 * b, -2 * a + b, -a + b;
    0, 0, 0;
    -a, 0, 0;
    -a - 2 * b, 0, -2 * a + b] : Matrix (Fin 5) (Fin 3) R) q.1 q.2

/-- The `k`-indexed right-hand side of the certificate identities `∑ psiAS · cPAS k = 5 * ·`:
the five values are `-b(a²-ab+b²)`, `-ag(a²-ab-b²)`, `2a²b`, `0`, `-2a²(a-2b)`. -/
def psiASval (a b g : R) : Fin 5 → R :=
  ![-(b * (a ^(2:ℕ) - a * b + b ^(2:ℕ))), -(a * g * (a ^(2:ℕ) - a * b - b ^(2:ℕ))),
    2 * a ^(2:ℕ) * b, 0, -(2 * a ^(2:ℕ) * (a - 2 * b))]

end Work.MotAS
