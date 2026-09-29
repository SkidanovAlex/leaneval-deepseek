import Mathlib
import Submission.Work.Cert.ACBall.Basic

/-! # The `bsqrt` residual bound, named

`bsqrt a sr si` is the principal-square-root ball `⟨sr, si, ⌈(a.r + E)·S/sr⌉ + 1⟩` where the exact
integer residual `E` bounds `S·|cx a.x a.y − (cx sr si)²|`.  This file only NAMES that residual, so
that the soundness proof can split into readable pieces. -/

namespace Work.Cert.ACBall

/-- The residual of `bsqrt`: with `X = |sr²−si²−a.x·S|` and `Y = |2·sr·si−a.y·S|`,
`bsqrtE a sr si = ⌊(X+Y)/S⌋ + 1 ≥ S·|cx a.x a.y − (cx sr si)²|`. -/
def bsqrtE (a : Bl) (sr si : ℤ) : ℤ :=
  fdiv (iabs (sr * sr - si * si - a.x * S) + iabs (2 * sr * si - a.y * S)) S + 1

/-- `bsqrt` in terms of `bsqrtE` (definitional unfolding). -/
lemma bsqrt_eq (a : Bl) (sr si : ℤ) :
    bsqrt a sr si = ⟨sr, si, dvu (a.r + bsqrtE a sr si) sr + 1⟩ := rfl

lemma bsqrt_r (a : Bl) (sr si : ℤ) :
    (bsqrt a sr si).r = dvu (a.r + bsqrtE a sr si) sr + 1 := rfl

end Work.Cert.ACBall
