/-
# ZeroFreeTables — SupDefs

The explicit real decomposition of `xyRe x t` into the "no-e" rational part `ReQ` and the
`exp (-(3x/2))`-weighted trigonometric part with coefficients `ReP`, `ImP`, obtained from the
closed form `Tf72FcClosed` for `tf72Fc (4/3)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- The "rational" (non-exponential) part of `Re (tf72Fc (4/3) (x + i t))`. -/
def ReQ (x t : ℝ) : ℝ :=
  (64/45)*(x/(x^2+t^2)) - (512/81)*((x^3-3*x*t^2)/(x^2+t^2)^3)
    + (1024/81)*((x^4-6*x^2*t^2+t^4)/(x^2+t^2)^4)
    - (16384/729)*((x^6-15*x^4*t^2+15*x^2*t^4-t^6)/(x^2+t^2)^6)

/-- The coefficient of `exp (-(3x/2)) * cos (3t/2)` in `Re (tf72Fc (4/3) (x + i t))`. -/
def ReP (x t : ℝ) : ℝ :=
  (1024/81)*((x^4-6*x^2*t^2+t^4)/(x^2+t^2)^4)
    + (8192/243)*((x^5-10*x^3*t^2+5*x*t^4)/(x^2+t^2)^5)
    + (16384/729)*((x^6-15*x^4*t^2+15*x^2*t^4-t^6)/(x^2+t^2)^6)

/-- The coefficient of `exp (-(3x/2)) * sin (3t/2)` in `Re (tf72Fc (4/3) (x + i t))`. -/
def ImP (x t : ℝ) : ℝ :=
  (1024/81)*((4*x*t^3-4*x^3*t)/(x^2+t^2)^4)
    + (8192/243)*((10*x^2*t^3-5*x^4*t-t^5)/(x^2+t^2)^5)
    + (16384/729)*((20*x^3*t^3-6*x^5*t-6*x*t^5)/(x^2+t^2)^6)

end Work.ZeroFreeTables.XY
