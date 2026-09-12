import Mathlib
/-!
# Coefficients of `∏ (X − C(c_i))` are algebraic integers when every `c_i` is

Standalone helper: expanding a monic product over complex numbers, the coefficient
at degree `m` is an integral (over `ℤ`) element whenever every root factor's
constant is integral.  (Prove by Finset induction using `IsIntegral.add`, `IsIntegral.mul`,
`IsIntegral.neg`, `IsIntegral.pow`; the empty product has coefficients `1` or `0`.)
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.CoeffIntegral

/-- One step of the induction: multiplying a polynomial all of whose coefficients
are integral by a fresh factor `X - C c` (with `c` integral) again gives a
polynomial all of whose coefficients are integral.  The coefficient recurrence
```
coeff (Q * (X - C c)) (k+1) = coeff Q k - c * coeff Q (k+1)
coeff (Q * (X - C c)) 0 = -(coeff Q 0) * c
```
follows from `Polynomial.coeff_mul_X` and `Polynomial.coeff_mul_C`. -/
private lemma mul_X_sub_C_coeff_isIntegral (Q : Polynomial ℂ) (c : ℂ)
    (hQ : ∀ m : ℕ, IsIntegral ℤ (Q.coeff m)) (hc : IsIntegral ℤ c) :
    ∀ m : ℕ, IsIntegral ℤ ((Q * (X - C c)).coeff m) := by
  intro m
  by_cases hm : m = 0
  · subst m
    have hx : (Q * (X - C c)).coeff 0 = -(Q.coeff 0) * c := by
      calc
        (Q * (X - C c)).coeff 0 = (Q * X - Q * (C c)).coeff 0 := by rw [mul_sub]
        _ = (Q * X).coeff 0 - (Q * (C c)).coeff 0 := by rw [coeff_sub]
        _ = 0 - Q.coeff 0 * c := by simp
        _ = -(Q.coeff 0) * c := by ring
    rw [hx]
    rw [show -(Q.coeff 0) * c = -((Q.coeff 0) * c) by ring]
    exact IsIntegral.neg (IsIntegral.mul (hQ 0) hc)
  · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨k, rfl⟩
    have hx : (Q * (X - C c)).coeff (k + 1) = Q.coeff k - Q.coeff (k + 1) * c := by
      calc
        (Q * (X - C c)).coeff (k + 1) = (Q * X - Q * (C c)).coeff (k + 1) := by rw [mul_sub]
        _ = (Q * X).coeff (k + 1) - (Q * (C c)).coeff (k + 1) := by rw [coeff_sub]
        _ = Q.coeff k - Q.coeff (k + 1) * c := by rw [coeff_mul_X, coeff_mul_C]
    rw [hx]
    exact IsIntegral.sub (hQ k) (IsIntegral.mul (hQ (k + 1)) hc)

/-- Finset version: the coefficients of `∏_{i ∈ s} (X - C(c i))` are all integral
over `ℤ`, proved by induction over the finset. -/
private lemma coeff_prod_finset_X_sub_C_isIntegral {ι : Type*} (c : ι → ℂ)
    (hint : ∀ i, IsIntegral ℤ (c i)) :
    ∀ (s : Finset ι) (m : ℕ),
      IsIntegral ℤ ((∏ i ∈ s, (X - C (c i))).coeff m) := by
  classical
  intro s
  refine Finset.induction_on s ?empty ?insert
  · intro m
    by_cases hm : m = 0
    · subst m
      rw [Finset.prod_empty]
      simp
      exact isIntegral_one
    · rw [Finset.prod_empty]
      rw [show (1 : Polynomial ℂ).coeff m = 0 by
        rw [Polynomial.coeff_one, if_neg hm]]
      exact isIntegral_zero
  · intro a s ha ih m
    rw [Finset.prod_insert ha]
    rw [mul_comm]
    exact mul_X_sub_C_coeff_isIntegral (∏ i ∈ s, (X - C (c i))) (c a) ih (hint a) m

theorem coeff_prod_X_sub_C_isIntegral {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hint : ∀ i, IsIntegral ℤ (c i)) (m : ℕ) :
    IsIntegral ℤ ((∏ i, (X - C (c i))).coeff m) := by
  classical
  simpa using (coeff_prod_finset_X_sub_C_isIntegral c hint Finset.univ m)

end Submission.CoeffIntegral
