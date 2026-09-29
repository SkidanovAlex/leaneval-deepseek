import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- If `u, v ∈ K[X]` are coprime over a field `K` and their Wronskian
`u'·v - u·v'` vanishes, then both derivatives vanish.  (Equivalently, the
logarithmic derivatives of `u` and `v` agree, which together with coprimality
forces `u'/u = v'/v` to be the derivative of a constant.) -/
theorem derivative_mul_sub_eq_zero_of_isCoprime {K : Type*} [Field K] (u v : Polynomial K) (hcop : IsCoprime u v) (h : u.derivative * v - u * v.derivative = 0) : u.derivative = 0 ∧ v.derivative = 0 := by
  -- Rewrite the hypothesis as `u'·v = u·v'`.
  have h' : u.derivative * v = u * v.derivative := sub_eq_zero.mp h
  -- `u ∣ u'·v`, and `u` is coprime to `v`, so `u ∣ u'`.
  have hu_dvd : u ∣ u.derivative :=
    hcop.dvd_of_dvd_mul_right ⟨v.derivative, h'⟩
  -- `v ∣ u·v'`, and `v` is coprime to `u`, so `v ∣ v'`.
  have hv_dvd : v ∣ v.derivative :=
    hcop.symm.dvd_of_dvd_mul_left ⟨u.derivative, by rw [mul_comm v u.derivative]; exact h'.symm⟩
  -- A polynomial dividing its own derivative has vanishing derivative.
  exact ⟨Polynomial.dvd_derivative_iff.mp hu_dvd, Polynomial.dvd_derivative_iff.mp hv_dvd⟩

end Commons.Algebra.Polynomial