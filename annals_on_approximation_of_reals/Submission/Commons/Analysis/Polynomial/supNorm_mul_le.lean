import Mathlib.Analysis.Polynomial.Norm

open scoped BigOperators
open Polynomial

namespace Commons.Analysis.Polynomial

/-- Sum of coefficient-product norms in the convolution defining `(P * Q).coeff i`,
bounded by `(natDegree P + 1) * supNorm P * supNorm Q`. -/
lemma supNorm_mul_le_sum_bound {A : Type*} [NormedRing A] (P Q : Polynomial A) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), ‖P.coeff j * Q.coeff (i - j)‖ ≤
      (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := by
  let N : ℕ := P.natDegree
  let S : ℝ := P.supNorm * Q.supNorm
  have hS : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg P.supNorm_nonneg Q.supNorm_nonneg
  have hterm : ∀ j, ‖P.coeff j * Q.coeff (i - j)‖ ≤ (if j ≤ N then S else 0) := by
    intro j
    by_cases hj : j ≤ N
    · have h1 := norm_mul_le (P.coeff j) (Q.coeff (i - j))
      have h2 : ‖P.coeff j‖ ≤ P.supNorm := Polynomial.le_supNorm P j
      have h3 : ‖Q.coeff (i - j)‖ ≤ Q.supNorm := Polynomial.le_supNorm Q (i - j)
      have hmul : ‖P.coeff j‖ * ‖Q.coeff (i - j)‖ ≤ P.supNorm * Q.supNorm :=
        mul_le_mul h2 h3 (norm_nonneg _) P.supNorm_nonneg
      simp [hj, S]
      exact h1.trans hmul
    · have hz : P.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hj)
      simp [hj, S, hz]
  calc
    ∑ j ∈ Finset.range (i + 1), ‖P.coeff j * Q.coeff (i - j)‖
        ≤ ∑ j ∈ Finset.range (i + 1), (if j ≤ N then S else 0) :=
          Finset.sum_le_sum (fun j _ => hterm j)
    _ = ∑ j ∈ Finset.range (i + 1), S * (if j ≤ N then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj' : j ≤ N <;> simp [hj']
    _ = S * (∑ j ∈ Finset.range (i + 1), (if j ≤ N then (1 : ℝ) else 0)) := by
        rw [← Finset.mul_sum]
    _ = S * (((Finset.range (i + 1)).filter (fun j => j ≤ N)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ S * (N + 1 : ℝ) := by
        have hsub : (Finset.range (i + 1)).filter (fun j => j ≤ N) ⊆ Finset.range (N + 1) := by
          intro j hj
          simp at hj ⊢
          exact hj.2
        have hcard : (((Finset.range (i + 1)).filter (fun j => j ≤ N)).card : ℝ) ≤ (N + 1 : ℝ) := by
          exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
        exact mul_le_mul_of_nonneg_left hcard hS
    _ = (N + 1 : ℝ) * S := by ring
    _ = (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := by
        simp [N, S]
        ring

/-- Every coefficient of the product satisfies the claimed bound. -/
lemma supNorm_mul_le_coeff {A : Type*} [NormedRing A] (P Q : Polynomial A) (i : ℕ) :
    ‖(P * Q).coeff i‖ ≤ (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := by
  calc
    ‖(P * Q).coeff i‖
        = ‖∑ j ∈ Finset.range (i + 1), P.coeff j * Q.coeff (i - j)‖ := by
          rw [Polynomial.coeff_mul]
          rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => P.coeff k * Q.coeff l) i]
    _ ≤ ∑ j ∈ Finset.range (i + 1), ‖P.coeff j * Q.coeff (i - j)‖ := norm_sum_le _ _
    _ ≤ (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := supNorm_mul_le_sum_bound P Q i

theorem supNorm_mul_le {A : Type*} [NormedRing A] (P Q : Polynomial A) :
    (P * Q).supNorm ≤ (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := by
  obtain ⟨i, hi⟩ := (P * Q).exists_eq_supNorm
  calc
    (P * Q).supNorm = ‖(P * Q).coeff i‖ := hi
    _ ≤ (P.natDegree + 1 : ℝ) * P.supNorm * Q.supNorm := supNorm_mul_le_coeff P Q i

end Commons.Analysis.Polynomial