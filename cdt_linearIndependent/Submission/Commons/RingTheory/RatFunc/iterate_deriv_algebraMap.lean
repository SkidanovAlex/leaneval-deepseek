import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.RingTheory.RatFunc

/-- The iterated derivative of a polynomial, seen inside the field of rational
functions: if `D` is the derivative on `K(X)` then `D^i` of the image of `p ∈ K[X]`
is the image of `p^{(i)}`. -/
theorem iterate_deriv_algebraMap {K : Type*} [Field K] (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (i : ℕ) (p : Polynomial K) :
    (D : RatFunc K → RatFunc K)^[i] (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.derivative^[i] p) := by
  induction i generalizing p with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hd, Function.iterate_succ_apply']

end Commons.RingTheory.RatFunc