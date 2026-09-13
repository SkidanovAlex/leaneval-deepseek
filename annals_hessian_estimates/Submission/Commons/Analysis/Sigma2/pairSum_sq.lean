import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Analysis.Sigma2

/-! Basic identity relating (sum of entries)^2, sum of squares, and the sum over unordered pairs (the latter in the iterated form `∑ j, ∑ i < j` used for sigma_2 of an eigenvalue tuple). -/
open scoped BigOperators

private lemma ite_lt_trichotomy {n : ℕ} (i j : Fin n) (x : ℝ) :
    x = (if i = j then x else 0) + (if i < j then x else 0) + (if j < i then x else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · have hji : ¬ j < i := lt_asymm h
    have hij : ¬ i = j := h.ne
    simp [h, hji, hij]
  · subst h
    simp
  · have hij : ¬ i < j := lt_asymm h
    have hne : ¬ i = j := (ne_of_lt h).symm
    simp [h, hij, hne]

theorem pairSum_sq {n : ℕ} (a : Fin n → ℝ) :
    (∑ i : Fin n, a i) ^ 2 =
      (∑ i : Fin n, (a i) ^ 2) + 2 * (∑ j : Fin n, ∑ i : Fin n, if i < j then a i * a j else 0) := by
  let M : ℝ := ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0
  let R : ℝ := ∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0
  let P : ℝ := ∑ j : Fin n, ∑ i : Fin n, if i < j then a i * a j else 0
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
        (∑ i : Fin n, ∑ j : Fin n, if i = j then a i * a j else 0) +
          (∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0) +
            (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
          ∑ i : Fin n, ((∑ j : Fin n, if i = j then a i * a j else 0) +
            (∑ j : Fin n, if i < j then a i * a j else 0) +
              (∑ j : Fin n, if j < i then a i * a j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact ite_lt_trichotomy i j (a i * a j)
      _ = (∑ i : Fin n, ∑ j : Fin n, if i = j then a i * a j else 0) +
          (∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0) +
            (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) := by
        simp [Finset.sum_add_distrib, add_assoc]
  have hdiag : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i * a j else 0) =
      ∑ i : Fin n, a i * a i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.sum_ite_eq]
  have hP : P = M := by
    dsimp [P, M]
    rw [Finset.sum_comm]
  have hR : R = M := by
    dsimp [R]
    calc
      (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
          ∑ j : Fin n, ∑ i : Fin n, if i < j then a j * a i else 0 := by rfl
      _ = (∑ j : Fin n, ∑ i : Fin n, if i < j then a i * a j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
      _ = M := by
        dsimp [M]
        rw [Finset.sum_comm]
  have hmainsq : (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, a i * a i) + M + R := by
    calc
      (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, a i) * (∑ i : Fin n, a i) := by rw [pow_two]
      _ = ∑ i : Fin n, ∑ j : Fin n, a i * a j := by rw [Fintype.sum_mul_sum]
      _ = (∑ i : Fin n, ∑ j : Fin n, if i = j then a i * a j else 0) +
          (∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0) +
            (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) := hsplit
      _ = (∑ i : Fin n, a i * a i) + M + R := by
        rw [hdiag]
  calc
    (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, a i * a i) + M + R := hmainsq
    _ = (∑ i : Fin n, (a i) ^ 2) + 2 * P := by
      rw [hR, hP]
      simp [pow_two, two_mul, add_assoc]

end Commons.Analysis.Sigma2