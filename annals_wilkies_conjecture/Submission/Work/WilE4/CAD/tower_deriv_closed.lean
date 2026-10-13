import Mathlib
import Submission.Work.WilE4.Tower
import Submission.Work.WilE4.Poly.iterate_pderiv_zero

namespace Work.WilE4.CAD

open MvPolynomial

/-- The derivative tower is closed under differentiation in the last variable, in the weak sense
that the derivative of a member is either `0` or again a member of the tower.  Indeed a member has
the form `(∂/∂X_m)^[k] P` with `k ≤ deg_{X_m} P`; if `k < deg_{X_m} P` then `k + 1` is still in the
range of the tower, and otherwise `k = deg_{X_m} P` and one more derivative kills `P`. -/
theorem tower_deriv_closed {m : ℕ} (H : List (MvPolynomial (Fin (m + 1)) ℝ)) :
    ∀ Q ∈ tower H, MvPolynomial.pderiv (Fin.last m) Q = 0 ∨
      MvPolynomial.pderiv (Fin.last m) Q ∈ tower H := by
  intro Q hQ
  simp only [tower, List.mem_flatMap, List.mem_map, List.mem_range] at hQ
  obtain ⟨P, hP, k, hk, hQk⟩ := hQ
  rw [← hQk, ← Function.iterate_succ_apply' (MvPolynomial.pderiv (Fin.last m)) k P]
  by_cases hcase : k + 1 < P.degreeOf (Fin.last m) + 1
  · right
    rw [tower, List.mem_flatMap]
    exact ⟨P, hP, List.mem_map.mpr ⟨k + 1, List.mem_range.mpr hcase, rfl⟩⟩
  · left
    exact Work.WilE4.Poly.iterate_pderiv_zero P (Fin.last m) (by omega)

end Work.WilE4.CAD
