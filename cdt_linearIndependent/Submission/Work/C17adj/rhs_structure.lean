import Mathlib
import Submission.Work.C17adj.divisor_defs

/-!
# Structure of the right-hand side `Σ_i c_i y^{i−4} y'`

For `y = x²/(x−1)` (so `y' = x(x−2)/(x−1)²`), each summand of the right hand side satisfies

`y^{i−4} y' = x^{2i}(x−2)(x−1)^{5−i} / (x⁷(x−1)³)`,

so that `Σ_i c_i y^{i−4} y'` is the rational function whose numerator is the explicit
polynomial `PsiNum c = Σ_i c_i x^{2i}(x−2)(x−1)^{5−i}` (of degree `≤ 11`) over the common
denominator `x⁷(x−1)³`.
-/

open Polynomial

namespace Work.C17adj

noncomputable section

set_option maxHeartbeats 8000000

/-- Degree bound for one summand of `PsiNum`: `C a · X^n · (X − 2) · (X − 1)^m` has degree
at most `n + 1 + m`. -/
private lemma natDegree_term_le (a : ℂ) (n m : ℕ) :
    (Polynomial.C a * Polynomial.X ^ n * (Polynomial.X - Polynomial.C (2 : ℂ))
      * (Polynomial.X - Polynomial.C (1 : ℂ)) ^ m).natDegree ≤ n + 1 + m := by
  calc (Polynomial.C a * Polynomial.X ^ n * (Polynomial.X - Polynomial.C (2 : ℂ))
        * (Polynomial.X - Polynomial.C (1 : ℂ)) ^ m).natDegree
      ≤ (Polynomial.C a * Polynomial.X ^ n * (Polynomial.X - Polynomial.C (2 : ℂ))).natDegree
        + ((Polynomial.X - Polynomial.C (1 : ℂ)) ^ m).natDegree := natDegree_mul_le
    _ ≤ (n + 1) + m := by
        gcongr
        · calc (Polynomial.C a * Polynomial.X ^ n * (Polynomial.X - Polynomial.C (2 : ℂ))).natDegree
              ≤ (Polynomial.C a * Polynomial.X ^ n).natDegree
                + (Polynomial.X - Polynomial.C (2 : ℂ)).natDegree := natDegree_mul_le
            _ ≤ n + 1 := by
                have h1 : (Polynomial.C a * Polynomial.X ^ n).natDegree ≤ n :=
                  (natDegree_C_mul_le a (Polynomial.X ^ n)).trans (le_of_eq (natDegree_X_pow n))
                have h2 : (Polynomial.X - Polynomial.C (2 : ℂ)).natDegree = 1 := natDegree_X_sub_C 2
                omega
        · calc ((Polynomial.X - Polynomial.C (1 : ℂ)) ^ m).natDegree
              ≤ m * (Polynomial.X - Polynomial.C (1 : ℂ)).natDegree := natDegree_pow_le
            _ = m := by rw [natDegree_X_sub_C]; ring

theorem rhs_structure (c : Fin 6 → ℂ) :
    (Work.C17adj.PsiNum c).natDegree ≤ 11 ∧
      Work.C17adj.RhsC c
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Work.C17adj.PsiNum c)
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ 7 * (Polynomial.X - 1) ^ 3) := by
  constructor
  · -- degree bound: every summand of `PsiNum c` has degree at most `2i + 1 + (5 − i) = i + 6 ≤ 11`
    rw [Work.C17adj.PsiNum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine (natDegree_term_le (c i) (2 * (i : ℕ)) (5 - (i : ℕ))).trans ?_
    have hi : (i : ℕ) < 6 := i.isLt
    omega
  · -- the rational-function identity: a summand-by-summand computation
    have hmul : ∀ i : Fin 6,
        algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc
          = algebraMap (Polynomial ℂ) (RatFunc ℂ)
              (Polynomial.C (c i) * Polynomial.X ^ (2 * (i : ℕ)) * (Polynomial.X - Polynomial.C 2)
                * (Polynomial.X - Polynomial.C 1) ^ (5 - (i : ℕ)))
            / algebraMap (Polynomial ℂ) (RatFunc ℂ)
                (Polynomial.X ^ 7 * (Polynomial.X - Polynomial.C 1) ^ 3) := by
      intro i
      fin_cases i <;>
        · norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.reduceFinMk, Fin.mk.injEq,
            id_eq, Fin.val_mk, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceSub,
            Nat.reduceMul, OfNat.ofNat]
          simp only [Work.C17.yQc, Work.C17.dyQc]
          simp only [map_mul, map_pow, RatFunc.algebraMap_C, map_sub, map_one, map_ofNat]
          field_simp
          rw [RatFunc.algebraMap_eq_C]
          ring
    rw [Work.C17adj.RhsC]
    rw [Finset.sum_congr rfl (fun i _ => hmul i)]
    rw [← Finset.sum_div]
    congr 1
    rw [Work.C17adj.PsiNum, map_sum]

end

end Work.C17adj
