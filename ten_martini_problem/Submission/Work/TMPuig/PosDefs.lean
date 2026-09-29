import Mathlib
import Submission.Work.TMC13.Basic
import Submission.Work.TMComp.RotBasics.Defs

/-!
# Definitions for the Puig positive lift (`pos_lift_exists`)

The positive projective lift of an upper triangular `SL(2,ℝ)`-matrix
`!![r,q;0,1/r]` (`r > 0`) is written as the composition of three Prüfer steps, using the
factorization of that matrix into three companion matrices `comp a = !![a,-1;1,0]`
(whose positive lift is `pruferStep a`):

`!![r,q;0,1/r] = comp (r*(q-1)) * comp (-(1/r)) * comp (-r)`.

This file only fixes the notation; the properties are proved in the neighbouring modules.
-/

namespace Work.TMPuig

noncomputable section

open Matrix
open scoped Matrix

/-- Positive projective lift of the upper triangular matrix `!![r,q;0,1/r]`, `r > 0`,
as a composition of three Prüfer steps. -/
def upperLiftC (r q t : ℝ) : ℝ :=
  Work.TMContract.pruferStep (r * (q - 1))
    (Work.TMContract.pruferStep (-(1 / r)) (Work.TMContract.pruferStep (-r) t))

end

end Work.TMPuig
