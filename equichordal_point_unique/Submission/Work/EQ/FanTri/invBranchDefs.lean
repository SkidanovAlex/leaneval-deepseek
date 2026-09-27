import Mathlib
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.Defs

/-!
# The unit direction `(1, v)/√(1+v²)`

For the uniform Lipschitz bound of the backward branch `invBranch a s` on a small disc around an
axis point `c = -1/2 + 2k`, the branch is written as `-Q + μ • unitDir v` where `v` is the ratio
`Q.2 / (Q.1 + a/2)` and `μ` is a complex number of modulus one depending on the branch sign `s`
and on the sign of `c + a/2`.  The pieces are:

* `unitDir v = ((1+v²)^(-1/2), v (1+v²)^(-1/2))`, the normalised direction of `(1,v)`; it is
  Lipschitz on `‖v‖ ≤ 1/2`;
* `v ↦ Q.2 / (Q.1 + a/2)` is Lipschitz on the disc (the denominator stays `≥ 3(1-a)/8`).
-/

namespace Work.EQ.FanTri

open Complex

noncomputable section

/-- The normalised direction of the pair `(1, v)`: `(1, v)/√(1+v²)`, with the principal square
root of `1 + v²`.  For `‖v‖ ≤ 1/2` this is a Lipschitz function of `v`. -/
def unitDir (v : ℂ) : ℂ × ℂ := ((sqHalf (v ^ 2))⁻¹, v * (sqHalf (v ^ 2))⁻¹)

@[simp] lemma unitDir_fst (v : ℂ) : (unitDir v).1 = (sqHalf (v ^ 2))⁻¹ := rfl

@[simp] lemma unitDir_snd (v : ℂ) : (unitDir v).2 = v * (sqHalf (v ^ 2))⁻¹ := rfl

end

end Work.EQ.FanTri
