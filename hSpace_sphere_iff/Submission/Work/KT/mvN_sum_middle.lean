import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.sumMvN

namespace Work.KT

open Matrix

noncomputable section

/-- **The middle-four exchange for block sums.**  For idempotents `p, q, r, s`, the two ways of
grouping the four blocks into a `2 × 2` block matrix on the diagonal agree up to Murray–von
Neumann equivalence: `(p ⊕ q) ⊕ (r ⊕ s) ~ (p ⊕ r) ⊕ (q ⊕ s)`.

Block sum is a commutative monoid operation up to `Mat.MvN`, so both sides are bracketings of the
same multiset `{p, q, r, s}`; the proof is the obvious chain of applications of associativity,
commutativity and the fact that `Mat.MvN` is a congruence for `Mat.sum` (`mvN_sum`), glued with
`Mat.mvN_trans`. -/
theorem mvN_sum_middle (R : Type) [Ring R] (p q r s : Mat R)
    (hp : p.IsIdem) (hq : q.IsIdem) (hr : r.IsIdem) (hs : s.IsIdem) :
    Mat.MvN ((p.sum q).sum (r.sum s)) ((p.sum r).sum (q.sum s)) := by
  have i1 : ((p.sum q).sum (r.sum s)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hp hq) (Mat.sum_idem hr hs)
  have i2 : (p.sum (q.sum (r.sum s))).IsIdem :=
    Mat.sum_idem hp (Mat.sum_idem hq (Mat.sum_idem hr hs))
  have i3 : (p.sum ((q.sum r).sum s)).IsIdem :=
    Mat.sum_idem hp (Mat.sum_idem (Mat.sum_idem hq hr) hs)
  have i4 : (p.sum ((r.sum q).sum s)).IsIdem :=
    Mat.sum_idem hp (Mat.sum_idem (Mat.sum_idem hr hq) hs)
  have i5 : ((p.sum (r.sum q)).sum s).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hp (Mat.sum_idem hr hq)) hs
  have i6 : (((p.sum r).sum q).sum s).IsIdem :=
    Mat.sum_idem (Mat.sum_idem (Mat.sum_idem hp hr) hq) hs
  have i7 : ((p.sum r).sum (q.sum s)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hp hr) (Mat.sum_idem hq hs)
  have h1 : Mat.MvN ((p.sum q).sum (r.sum s)) (p.sum (q.sum (r.sum s))) :=
    mvN_sum_assoc p q (r.sum s)
  have h2 : Mat.MvN (p.sum (q.sum (r.sum s))) (p.sum ((q.sum r).sum s)) :=
    mvN_sum (Mat.mvN_refl hp) (Mat.mvN_symm (mvN_sum_assoc q r s))
  have h3 : Mat.MvN (p.sum ((q.sum r).sum s)) (p.sum ((r.sum q).sum s)) :=
    mvN_sum (Mat.mvN_refl hp) (mvN_sum (mvN_sum_comm q r) (Mat.mvN_refl hs))
  have h4 : Mat.MvN (p.sum ((r.sum q).sum s)) ((p.sum (r.sum q)).sum s) :=
    Mat.mvN_symm (mvN_sum_assoc p (r.sum q) s)
  have h5 : Mat.MvN ((p.sum (r.sum q)).sum s) (((p.sum r).sum q).sum s) :=
    mvN_sum (Mat.mvN_symm (mvN_sum_assoc p r q)) (Mat.mvN_refl hs)
  have h6 : Mat.MvN (((p.sum r).sum q).sum s) ((p.sum r).sum (q.sum s)) :=
    mvN_sum_assoc (p.sum r) q s
  exact Mat.mvN_trans i1 i2 i7 h1
    (Mat.mvN_trans i2 i3 i7 h2
      (Mat.mvN_trans i3 i4 i7 h3
        (Mat.mvN_trans i4 i5 i7 h4
          (Mat.mvN_trans i5 i6 i7 h5 h6))))

end

end Work.KT
