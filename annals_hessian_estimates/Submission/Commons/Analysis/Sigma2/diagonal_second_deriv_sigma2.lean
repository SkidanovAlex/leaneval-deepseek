import Mathlib

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem diagonal_second_deriv_sigma2 (lam : Fin 4 → ℝ) (A : Fin 4 → Fin 4 → ℝ)
    (B : Fin 4 → Fin 4 → ℝ) (C : Fin 4 → Fin 4 → ℝ)
    (hdiag : ∀ i j, A i j = if i = j then lam i else 0)
    (hBsym : ∀ i j, B i j = B j i)
    (hraw : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        C i i * A j j + B i i * B j j + B i i * B j j + A i i * C j j
          - 2 * B i j * B i j - 2 * A i j * C i j else 0) = 0) :
    (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * C i i) =
      (∑ i : Fin 4, ∑ j : Fin 4, B i j ^ 2) - (∑ i : Fin 4, B i i) ^ 2 := by
  have hkey : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * C i i)
      - ((∑ i : Fin 4, ∑ j : Fin 4, B i j ^ 2) - (∑ i : Fin 4, B i i) ^ 2)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
          C i i * A j j + B i i * B j j + B i i * B j j + A i i * C j j
            - 2 * B i j * B i j - 2 * A i j * C i j else 0) := by
    simp only [Fin.sum_univ_four]
    simp only [hdiag]
    simp only [hBsym 1 0, hBsym 2 0, hBsym 3 0, hBsym 2 1, hBsym 3 1, hBsym 3 2]
    simp
    ring
  have h0 : (∑ i : Fin 4, ((∑ t : Fin 4, lam t) - lam i) * C i i)
      - ((∑ i : Fin 4, ∑ j : Fin 4, B i j ^ 2) - (∑ i : Fin 4, B i i) ^ 2) = 0 := by
    rw [hkey, hraw]
  exact sub_eq_zero.mp h0

end Commons.Analysis.Sigma2
