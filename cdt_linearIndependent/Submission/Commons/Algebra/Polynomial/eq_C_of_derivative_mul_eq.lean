import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- **The constants of a differential field, in polynomial form.**  If `p, q ∈ K[X]` are
coprime over a field `K` of characteristic zero and `q · p' = p · q'` (i.e. the rational
function `p/q` has zero derivative), then `q` is constant. -/
theorem eq_C_of_derivative_mul_eq {K : Type*} [Field K] [CharZero K] {p q : Polynomial K}
    (hcop : IsCoprime p q) (h : q * p.derivative = p * q.derivative) :
    ∃ c : K, q = Polynomial.C c := by
  -- `q ∣ q'`: from `q · p' = p · q'` we get `q ∣ p · q' = q' · p`, and since
  -- `q` is coprime to `p` this forces `q ∣ q'`.
  have hq_dvd : q ∣ q.derivative :=
    hcop.symm.dvd_of_dvd_mul_right ⟨p.derivative, by rw [mul_comm q.derivative p, ← h]⟩
  -- A polynomial dividing its own derivative has vanishing derivative.
  have hderiv : q.derivative = 0 := Polynomial.dvd_derivative_iff.mp hq_dvd
  exact ⟨q.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hderiv⟩

end Commons.Algebra.Polynomial