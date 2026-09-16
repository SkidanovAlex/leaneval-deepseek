import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Inductions

open Polynomial

namespace Commons.Algebra.Polynomial

theorem divX_natDegree_lt {K : Type*} [CommRing K] {p : Polynomial K} (h0 : p.coeff 0 = 0)
    (hp : p ≠ 0) : p.divX ≠ 0 ∧ p.divX.natDegree < p.natDegree := by
  have hdivX : p.divX ≠ 0 := by
    intro h
    have : p = C (p.coeff 0) := divX_eq_zero_iff.mp h
    rw [h0, C_0] at this
    exact hp this
  refine ⟨hdivX, ?_⟩
  rw [natDegree_divX_eq_natDegree_tsub_one]
  apply Nat.sub_lt
  · by_contra h
    rw [not_lt, Nat.le_zero] at h
    exact hp (by rw [eq_C_of_natDegree_eq_zero h, h0, C_0])
  · norm_num

end Commons.Algebra.Polynomial