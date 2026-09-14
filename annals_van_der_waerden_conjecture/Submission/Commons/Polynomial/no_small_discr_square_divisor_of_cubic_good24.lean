import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option maxHeartbeats 800000

namespace Commons.Polynomial

private lemma no_small_neg_square_divisor {k : ℤ}
    (hk : k = -23 ∨ k = -31 ∨ k = -59 ∨ k = -83 ∨ k = -87 ∨ k = -107 ∨
      k = -116 ∨ k = -139 ∨ k = -140) {m D : ℤ}
    (hDneg : D < 0) (hDle : |D| ≤ 22) (hm : k = m ^ 2 * D) : False := by
  have hDdvd : D ∣ k := by
    rw [hm]
    exact dvd_mul_left D (m ^ 2)
  have hD_ge : -22 ≤ D := by
    have h := abs_le.mp (show |D| ≤ 22 by exact hDle)
    omega
  have hD_le1 : D ≤ -1 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    interval_cases D <;> norm_num at hDdvd
    all_goals
      have hmsq_nonneg : 0 ≤ m ^ 2 := sq_nonneg m
      have hmsq_lt : m ^ 2 < 12 ^ 2 := by nlinarith
      have hm_lt : m < 12 := by nlinarith [sq_nonneg (m - 12)]
      have hm_gt : -12 < m := by nlinarith [sq_nonneg (m + 12)]
      interval_cases m <;> norm_num at hm

private lemma discr_cubic_good24_values (a b c : ℤ)
    (h : (a, b, c) ∈ [(-2,1,1), (-2,1,2), (-2,2,1), (-2,3,-1), (-1,0,1), (-1,1,2), (-1,2,-1), (-1,2,1), (-1,3,-2), (0,1,-1), (0,1,1), (0,2,-2), (0,2,-1), (0,2,1), (0,2,2), (1,0,-1), (1,1,-2), (1,2,-1), (1,2,1), (1,3,2), (2,1,-2), (2,1,-1), (2,2,-1), (2,3,1)]) :
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-23 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-31 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-59 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-83 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-87 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-107 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-116 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-139 : ℚ) ∨
    Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = (-140 : ℚ) := by
  simp at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    rw [Polynomial.discr_of_degree_eq_three (by compute_degree!)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X]
    norm_num

theorem no_small_discr_square_divisor_of_cubic_good24 (a b c : ℤ)
    (h : (a, b, c) ∈ [(-2,1,1), (-2,1,2), (-2,2,1), (-2,3,-1), (-1,0,1), (-1,1,2), (-1,2,-1), (-1,2,1), (-1,3,-2), (0,1,-1), (0,1,1), (0,2,-2), (0,2,-1), (0,2,1), (0,2,2), (1,0,-1), (1,1,-2), (1,2,-1), (1,2,1), (1,3,2), (2,1,-2), (2,1,-1), (2,2,-1), (2,3,1)])
    {m D : ℤ} (hDneg : D < 0) (hDle : |D| ≤ 22)
    (hm : Polynomial.discr (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = ((m ^ 2 * D : ℤ) : ℚ)) :
    False := by
  have hvals := discr_cubic_good24_values a b c h
  rcases hvals with h23 | h31 | h59 | h83 | h87 | h107 | h116 | h139 | h140
  · exact no_small_neg_square_divisor (k := -23) (by left; rfl) hDneg hDle
      (by exact_mod_cast h23.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -31) (by right; left; rfl) hDneg hDle
      (by exact_mod_cast h31.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -59) (by right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h59.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -83) (by right; right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h83.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -87) (by right; right; right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h87.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -107) (by right; right; right; right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h107.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -116) (by right; right; right; right; right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h116.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -139) (by right; right; right; right; right; right; right; left; rfl) hDneg hDle
      (by exact_mod_cast h139.symm.trans hm)
  · exact no_small_neg_square_divisor (k := -140) (by right; right; right; right; right; right; right; right; rfl) hDneg hDle
      (by exact_mod_cast h140.symm.trans hm)

end Commons.Polynomial