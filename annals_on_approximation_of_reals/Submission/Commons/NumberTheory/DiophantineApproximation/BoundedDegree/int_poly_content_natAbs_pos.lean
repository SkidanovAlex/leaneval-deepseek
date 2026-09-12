import Mathlib.RingTheory.Polynomial.Content

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

theorem int_poly_content_natAbs_pos (P : Polynomial ℤ) (h : P ≠ 0) :
    1 ≤ P.content.natAbs := by
  have hc : P.content ≠ 0 := by
    intro hc0
    exact h (Polynomial.content_eq_zero_iff.mp hc0)
  exact Nat.succ_le_of_lt (Int.natAbs_pos.mpr hc)

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree