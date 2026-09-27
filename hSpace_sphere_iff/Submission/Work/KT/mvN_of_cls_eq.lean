import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.sumMvN
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.sum_mvN_assoc
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.monoid_grothendieck
import Submission.Work.KT.cls_eq_stable_mvN

namespace Work.KT

/-- **`K₀` is the Grothendieck group of the Murray–von Neumann monoid**: two idempotent matrices
with the same class in `K₀ R` are stably Murray–von Neumann equivalent, with the *same* identity
block added on both sides.  Route (self-contained): let `Q` be the quotient of the idempotent
matrices by `Mat.MvN` with the commutative-monoid structure induced by `Mat.sum` (well defined by
`sum_mvN_congr`; associative/commutative/unital up to `MvN` by `mvN_sum_assoc`, `mvN_sum_comm`,
`mvN_sum_one_zero`); use `monoid_grothendieck` to get the group completion `G` of `Q` with
`f a = f b ↔ ∃ c, a + c = b + c`; build the group hom `K0 R → G` sending `cls u` (idempotent `u`) to
`f (Quotient.mk u)` and non-idempotent generators to `0` (well defined by additivity of `f`,
`MvN`-invariance and `cls_eq_zero_of_not_idem`); conclude with the complement `1 - c` and
`mvN_sum_compl`, or with `rel_cancel`'s second conjunct. -/
theorem mvN_of_cls_eq {R : Type} [Ring R] {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    (h : cls p = cls q) : ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k)) :=
  -- This is exactly the statement of `Work.KT.k2_K0_detect`
  -- (`Submission/Work/KT/cls_eq_stable_mvN.lean`), which carries out precisely the route
  -- described above: the monoid `k2V R` of idempotents modulo `Mat.MvN` under block sum, the
  -- group completion `monoid_grothendieck (k2V R)`, the induced map `K0 R → G`, cancellation of
  -- the common block `c` via `rel_cancel`, and finally `mvN_sum_compl` for `c`.
  k2_K0_detect p q hp hq h

end Work.KT
