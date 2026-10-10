import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cubic `G4AS` and the parametrisation of its surface

Definitions only (no proofs): the cubic `G4AS = kleinRAS · 4` at the AS affine chart, and the
stereographic parametrisation of the quadric surface `Q₀ = {q₀ = 0}` (with
`q₀ = kleinPAS0(·, 0)`) used to show that the surface `{G4AS = 0}` is rational.

The target polar factor of the AS census is `cubAS a b g = -576 (a²-ab-b²) · G4AS a b g`
(`MotAS.cubAS_eq`), so the junk clause for `cubAS` is the junk clause for `G4AS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.MotAS

open MvPolynomial

/-- The affine chart `(0, X₀, X₁, X₂, 1)` used by the AS link (the same template as
`Work.MotK.chart3`). -/
noncomputable def chart3AS (R : Type*) [CommRing R] : Fin 5 → MvPolynomial (Fin 3) R :=
  ![0, X 0, X 1, X 2, 1]

/-- **The fourth component of the inverse AS chart map at the affine chart.**  The target polar
factor of the census is `-576 (a²-a b-b²)` times this cubic. -/
noncomputable def G4AS {R : Type*} [CommRing R] (a b g : R) : MvPolynomial (Fin 3) R :=
  kleinRAS (C a) (C b) (C g) (chart3AS R) 4

/-- `q₀ = kleinPAS0` with `y₄ = 0`: the quadratic form of the quadric surface `Q₀` that `R^AS`
maps the chart `{z₀ = 0}` into. -/
def coneQ {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  kleinPAS0 a b g ![y 0, y 1, y 2, y 3, 0]

/-- The polar form of `q₀`. -/
def coneB {R : Type*} [CommRing R] (a b g : R) (u v : Fin 5 → R) : R :=
  coneQ a b g (u + v) - coneQ a b g u - coneQ a b g v

/-- **The `K`-point `P = (0, a²+b², 0, a²-b²-a b, 0)` of `Q₀`.**  It is nonzero for every
`(a,b)` with `a²-a b-b² ≠ 0` (if `a²+b² = 0` then `a = 2b` and `a²-b²-a b = b² ≠ 0`), and
`q₀(P) = 5 a² b² (a²+b²)`. -/
def coneP {R : Type*} [CommRing R] (a b : R) : Fin 5 → R :=
  ![0, a ^ 2 + b ^ 2, 0, a ^ 2 - b ^ 2 - a * b, 0]

/-- The direction `d = (u, 1, v, 0, 0)` of the parametrisation chart `{d₃ = 0}`, in which the
coordinates are `(u,v)`. -/
noncomputable def coneD (R : Type*) [CommRing R] : Fin 5 → MvPolynomial (Fin 2) R :=
  ![X 0, 1, X 1, 0, 0]

/-- The stereographic parametrisation `y(u,v) = q₀(d)·P − b(P,d)·d` of `Q₀` from `P`, in the
direction `d = (u,1,v,0,0)`.  It is homogeneous of degree two in `d` and satisfies `q₀(y) = 0`. -/
noncomputable def paraY {R : Type*} [CommRing R] (a b g : R) : Fin 5 → MvPolynomial (Fin 2) R :=
  let P : Fin 5 → MvPolynomial (Fin 2) R := coneP (C a) (C b)
  let d : Fin 5 → MvPolynomial (Fin 2) R := coneD R
  fun i => coneQ (C a) (C b) (C g) d * P i - coneB (C a) (C b) (C g) P d * d i

/-- The parametrised coordinates `Y_i = kleinPAS_i(y(u,v))` of the target. -/
noncomputable def paraCoord {R : Type*} [CommRing R] (a b g : R) (i : Fin 5) :
    MvPolynomial (Fin 2) R :=
  kleinPAS (C a) (C b) (C g) (paraY a b g) i

end Work.MotAS
