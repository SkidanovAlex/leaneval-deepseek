import Mathlib
import Submission.Work.WilE2.sign_const_of_zeros_on_Ioo
import Submission.Work.WilE2.deriv_left_pos_of_pos_on_Ioo
import Submission.Work.WilE2.deriv_right_neg_of_pos_on_Ioo

namespace Work.WilE2

/-- **Sign of the derivatives at the two simple zeros.**

`f` is continuous on `[a, b]`, vanishes at `a` and at `b`, and has no zero in the open
interval `(a, b)`.  Hence `f` keeps a constant (strict) sign on `(a, b)`
(`sign_const_of_zeros_on_Ioo`), and a nonzero derivative at an endpoint points in the
direction in which `f` leaves `0`: at the left endpoint it has the sign of `f` on `(a, b)`,
at the right endpoint the opposite one.  Consequently the two derivatives have opposite
signs, so their product is negative.

The case `f < 0` on `(a, b)` is reduced to the positive case by replacing `f` with `-f`
(which swaps the signs of both derivatives). -/
theorem deriv_mul_neg_of_simple_zeros {f : ℝ → ℝ} {a b c d : ℝ} (hab : a < b)
    (hcont : Continuous f) (hfa : f a = 0) (hfb : f b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, f x ≠ 0)
    (ha : HasDerivAt f c a) (hb : HasDerivAt f d b) (hc : c ≠ 0) (hd : d ≠ 0) :
    c * d < 0 := by
  rcases sign_const_of_zeros_on_Ioo hab hcont hfa hne with hpos | hneg
  · -- `f > 0` on `(a, b)`: `c > 0` and `d < 0`.
    have hcpos : 0 < c := deriv_left_pos_of_pos_on_Ioo hab ha hfa hc hpos
    have hdneg : d < 0 := deriv_right_neg_of_pos_on_Ioo hab hb hfb hd hpos
    exact mul_neg_of_pos_of_neg hcpos hdneg
  · -- `f < 0` on `(a, b)`: apply the positive case to `-f`, which is `> 0` there.
    have hpos' : ∀ x ∈ Set.Ioo a b, 0 < (-f) x := fun x hx => by
      simpa using neg_pos.mpr (hneg x hx)
    have ha' : HasDerivAt (-f) (-c) a := ha.neg
    have hb' : HasDerivAt (-f) (-d) b := hb.neg
    have hc' : 0 < -c :=
      deriv_left_pos_of_pos_on_Ioo hab ha' (by simpa using hfa) (neg_ne_zero.mpr hc) hpos'
    have hd' : -d < 0 :=
      deriv_right_neg_of_pos_on_Ioo hab hb' (by simpa using hfb) (neg_ne_zero.mpr hd) hpos'
    have hcneg : c < 0 := neg_pos.mp hc'
    have hdpos : 0 < d := neg_lt_zero.mp hd'
    exact mul_neg_of_neg_of_pos hcneg hdpos

end Work.WilE2
