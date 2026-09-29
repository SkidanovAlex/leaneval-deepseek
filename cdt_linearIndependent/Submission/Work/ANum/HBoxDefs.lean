import Submission.Work.ANum.ACertD
import Submission.Work.ANum.hauptH_logDeriv

/-! # A box version of the `|h'/h|` bound

`Work.ANum.ACertD.hGrad` bounds `‖h'/h‖` at a *point* box.  The certificate needs the same bound
for every point of a small disc (the image of an arc under `psiA`), and the cheapest sound
way to get it is to run the *same* complex interval sum `hGradSum2` over the *inflated* box: the
sum's centre keeps the cancellation between the terms while the accumulated width is the cheap
"variation" part.

The identity making this possible is `Work.ANum.hauptH_logDeriv` (proved):
`h'/h = 1/q + 24 ∑_{n≥0} (n+1) qⁿ/(1+q^{n+1})`. -/

namespace Work.ANum

noncomputable section

open Submission.CDTPlan Complex

/-- Upper mantissa bound for `‖h'/h‖` on a rectangle `D` (which must avoid `0`): the finite
`M`-term complex interval sum (which keeps the cancellation of the terms), scaled by `24`, plus the
point `1/q` and the triangle tail `hGradTail`. -/
def hGradBox (D : CD) (M : ℕ) : ℤ :=
  absUp (((hGradSum2 D M 0 ONE (CD.pt 0 0)).mul (cst (Iv.pt (24 * SC)))).add D.inv)
    + hGradTail (absUp D) M

end

end Work.ANum
