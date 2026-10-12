import Mathlib.Data.Real.Basic
import Submission.Work.ChiSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional fibre kernel of the `chiSmall` bump

`chiSmall M z = chiSmallNormFactor M * (ζ(z₀)ζ(z₁)ζ(z₂))^M`, so the product of two
shifted bumps `chiSmall M (a-u) * chiSmall M (b-u)` is a positive constant times the
*coordinatewise product* `∏ j, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)` of the
one-dimensional kernels

    chiFibreK M A B t := (ζ(A − t) · ζ(B − t))^M .

This file only *defines* that kernel; the two consumer modules
`Submission.Work.BoseB1Cube.chiFibreWing`, `...chiFibreMass`, `...chiFibreProd`
prove the one-dimensional and product-structure facts about it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

open Submission.BoseGases

/-- The one-dimensional fibre kernel of the `chiSmall` bump at coordinate pair `(A,B)`:
`(ζ(A − t)·ζ(B − t))^M`. -/
noncomputable def chiFibreK (M : ℕ) (A B t : ℝ) : ℝ :=
  (zeta1d (A - t) * zeta1d (B - t)) ^ M

end Work.BoseB1Cube
