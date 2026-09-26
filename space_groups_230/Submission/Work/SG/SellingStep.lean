import Mathlib
import Submission.Work.SG.SellingDefs

/-! ## The Selling step on a superbase (`Work.SG.selling_reduce`)

This module fixes the *vocabulary* of the Selling reduction of `Work.SG.selling_reduce`: the
elementary operation `sellStep` on a superbase `v : Fin 4 → IVec` (four vectors summing to zero,
any three of which form a basis) together with the integer matrix `sellStepMat i j` realising it
on the column basis.

If `v = sb W` for a unimodular `W` and `bf Q (v i) (v j) > 0`, the Selling step replaces `W` by
`W * sellStepMat i j` (again unimodular), whose superbase is `sellStep (sb W) i j`, and the
"energy" `∑ m, qf Q (v m)` drops by `2 * bf Q (v i) (v j)`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- One **Selling step** on a superbase, at the ordered pair `(i,j)`: negate `v i`, keep `v j`
and add `v i` to the two remaining vectors.  The four new vectors again sum to zero. -/
def sellStep (v : Fin 4 → IVec) (i j : Fin 4) : Fin 4 → IVec :=
  fun m => if m = i then - v i else if m = j then v j else v m + v i

@[simp] theorem sellStep_apply (v : Fin 4 → IVec) (i j m : Fin 4) :
    sellStep v i j m = (if m = i then - v i else if m = j then v j else v m + v i) := rfl

/-- The integer matrix effecting the Selling step `sellStep · i j` on the column basis: its
`b`-th column is the `b`-th vector of `sellStep coordVec i j` (the step applied to the standard
superbase `coordVec`). -/
def sellStepMat (i j : Fin 4) : IMat := Matrix.of fun a b => sellStep coordVec i j b.succ a

@[simp] theorem sellStepMat_apply (i j : Fin 4) (a b : Fin 3) :
    sellStepMat i j a b = sellStep coordVec i j b.succ a := rfl

end Work.SG
