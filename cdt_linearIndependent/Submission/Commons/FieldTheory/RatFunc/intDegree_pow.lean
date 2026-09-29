import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.RatFunc

theorem intDegree_pow {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = n * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

end Commons.FieldTheory.RatFunc