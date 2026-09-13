import Mathlib

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem diagonal_first_deriv_sigma2 (lam : Fin 4 → ℝ) (A : Fin 4 → Fin 4 → ℝ)
    (B : Fin 4 → Fin 4 → Fin 4 → ℝ) (k : Fin 4)
    (hdiag : ∀ i j, A i j = if i = j then lam i else 0)
    (hraw : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        B k i i * A j j + A i i * B k j j - 2 * A i j * B k i j else 0) = 0) :
    (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * B k i i) = 0 := by
  have hkey : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * B k i i) =
      (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          B k i i * A j j + A i i * B k j j - 2 * A i j * B k i j else 0) := by
    simp only [Fin.sum_univ_four]
    simp only [hdiag]
    simp
    ring
  rw [hkey]
  exact hraw

end Commons.Analysis.Sigma2
