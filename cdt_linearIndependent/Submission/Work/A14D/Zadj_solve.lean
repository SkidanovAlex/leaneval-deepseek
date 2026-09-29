import Mathlib
import Submission.Work.A14D.Zadj_defs

/-!
# The final linear algebra for `Work.A14D.adjointZ_no_solution`

With `β = W/DZ`, `W = n₀ + n₁x + n₂x²` (`DZ = x²(x−1)`), the master identity
`PhiNumZ W = PsiZ c·x³(x−1)` becomes the polynomial equation

`PhiNumZ (Wlin n) − PsiZ c·x³(x−1) = 0`,

an explicit polynomial of degree `≤ 9` whose `X³..X⁹`-coefficients are the linear forms `LfZ n c d`.
Eliminating them (using the coefficients `3,4,5,6,8,9`) gives `n = 0` and `c = 0`; note that every
elementary operation is `ℂ`-linear algebra (`linear_combination`), not ordered arithmetic.
-/

open Polynomial

noncomputable section
namespace Work.A14D

/-- The coefficient of `X^d` in the cleared difference `PhiNumZ (Wlin n) − PsiZ c·x³(x−1)`
(and `0` for `d ∉ {3,…,9}`). -/
def LfZ (n c : Fin 3 → ℂ) : ℕ → ℂ
  | 3 => 4 * n 0 - 2 * c 2
  | 4 => -(34 * n 0) + n 1 + 7 * c 2
  | 5 => 84 * n 0 - 6 * n 1 + 2 * c 1 - 9 * c 2
  | 6 => -(90 * n 0) + 10 * n 1 - 2 * n 2 - 5 * c 1 + 5 * c 2
  | 7 => 36 * n 0 - 14 * n 1 - 4 * n 2 - 2 * c 0 + 4 * c 1 - c 2
  | 8 => 9 * n 1 + 6 * n 2 + 3 * c 0 - c 1
  | 9 => -c 0
  | _ => 0

/-- The explicit polynomial form of the cleared difference. -/
def GZpoly (n c : Fin 3 → ℂ) : Polynomial ℂ :=
  C (LfZ n c 3) * X ^ 3 + C (LfZ n c 4) * X ^ 4 + C (LfZ n c 5) * X ^ 5
    + C (LfZ n c 6) * X ^ 6 + C (LfZ n c 7) * X ^ 7 + C (LfZ n c 8) * X ^ 8
    + C (LfZ n c 9) * X ^ 9

lemma key_eq (n c : Fin 3 → ℂ) :
    PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1)) = GZpoly n c := by
  apply Polynomial.funext
  intro z
  simp [PhiNumZ, Wlin, GZpoly, DZ, P2Z, P1Z, P0Z, PsiZ, LfZ]
  ring

lemma coeff3 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 3 = 4 * n 0 - 2 * c 2 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num

lemma coeff4 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 4
      = -(34 * n 0) + n 1 + 7 * c 2 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num

lemma coeff5 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 5
      = 84 * n 0 - 6 * n 1 + 2 * c 1 - 9 * c 2 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num

lemma coeff6 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 6
      = -(90 * n 0) + 10 * n 1 - 2 * n 2 - 5 * c 1 + 5 * c 2 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num

lemma coeff8 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 8
      = 9 * n 1 + 6 * n 2 + 3 * c 0 - c 1 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num

lemma coeff9 (n c : Fin 3 → ℂ) :
    (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))).coeff 9 = -c 0 := by
  rw [key_eq]; unfold GZpoly LfZ
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]; norm_num


/-- A polynomial of degree `≤ 2` is its own `Wlin`-expansion. -/
lemma eq_Wlin_of_natDegree_le_two (W : Polynomial ℂ) (h : W.natDegree ≤ 2) :
    W = Wlin (fun k : Fin 3 => W.coeff (k : ℕ)) := by
  rw [W.as_sum_range_C_mul_X_pow' (by omega : W.natDegree < 3), Wlin,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp

theorem Zadj_solve (n : Fin 3 → ℂ) (c : Fin 3 → ℂ)
    (h : PhiNumZ (Wlin n) = PsiZ c * (X ^ 3 * (X - 1))) :
    n = 0 ∧ c = 0 := by
  have hzero : (PhiNumZ (Wlin n) - PsiZ c * (X ^ 3 * (X - 1))) = 0 := by rw [h]; ring
  have e3 : 4 * n 0 - 2 * c 2 = 0 := by
    have h' := coeff3 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have e4 : -(34 * n 0) + n 1 + 7 * c 2 = 0 := by
    have h' := coeff4 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have e5 : 84 * n 0 - 6 * n 1 + 2 * c 1 - 9 * c 2 = 0 := by
    have h' := coeff5 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have e6 : -(90 * n 0) + 10 * n 1 - 2 * n 2 - 5 * c 1 + 5 * c 2 = 0 := by
    have h' := coeff6 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have e8 : 9 * n 1 + 6 * n 2 + 3 * c 0 - c 1 = 0 := by
    have h' := coeff8 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have e9 : -c 0 = 0 := by
    have h' := coeff9 n c; rw [hzero, Polynomial.coeff_zero] at h'; exact h'.symm
  have hc0 : c 0 = 0 := by linear_combination -e9
  have hc2 : c 2 = 2 * n 0 := by linear_combination -(1 / 2) * e3
  have hn1 : n 1 = 20 * n 0 := by linear_combination e4 - 7 * hc2
  have hc1 : c 1 = 27 * n 0 := by
    linear_combination (1 / 2) * e5 + 3 * hn1 + (9 / 2) * hc2
  have hn2 : n 2 = -(51 / 2) * n 0 := by
    linear_combination (1 / 6) * e8 - (3 / 2) * hn1 - (1 / 2) * hc0 + (1 / 6) * hc1
  have hn0 : n 0 = 0 := by
    linear_combination (1 / 36) * e6 - (10 / 36) * hn1 + (2 / 36) * hn2
      + (5 / 36) * hc1 - (5 / 36) * hc2
  have h1 : n 1 = 0 := by rw [hn1, hn0]; ring
  have h2 : n 2 = 0 := by rw [hn2, hn0]; ring
  have hcc1 : c 1 = 0 := by rw [hc1, hn0]; ring
  have hcc2 : c 2 = 0 := by rw [hc2, hn0]; ring
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i
    · simpa using hn0
    · simpa using h1
    · simpa using h2
  · funext i
    fin_cases i
    · simpa using hc0
    · simpa using hcc1
    · simpa using hcc2

end Work.A14D
