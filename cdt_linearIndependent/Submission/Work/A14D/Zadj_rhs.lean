import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Commons.FieldTheory.RatFunc.ordAtT_div
import Submission.Commons.FieldTheory.RatFunc.ordAt_algebraMap

/-!
# `Work.A14D.Zadj_rhs` — the right hand side `Σ_{i<3} c_i y^{−i} y'` of the adjoint equation

For `y = x²/(x−1)`, so that `y' = x(x−2)/(x−1)²`, each summand `y^{−i}·y'` (`i = 0,1,2`)
satisfies

`y^{−i}·y' = x^{4−3i}(x−2)(x−1)^{2−i} / (x³(x−1)²) ,

hence the whole right hand side `RhsZ c = Σ_i c_i y^{−i} y'` is the rational function with
numerator the explicit polynomial `PsiZ c` (of degree `≤ 5`) over the common denominator
`QZ = x³(x−1)²`.  Consequently its order of vanishing `ordAtT α` is

`rootMultiplicity α (PsiZ c) − rootMultiplicity α QZ`,

and since the first term is a natural number while the second equals `3` at `α = 0`, `2` at
`α = 1` and `0` otherwise, the order is bounded below by `−3` at `x = 0`, by `−2` at `x = 1`
and by `0` elsewhere.  These are exactly the exponents of the singularities `x = 0`, `x = 1`
of the adjoint equation.
-/

open Polynomial

namespace Work.A14D

noncomputable section

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- The numerator of the summand `y^{−i}·y'` over the common denominator `QZ = x³(x−1)²`. -/
private def rnZ (i : Fin 3) : Polynomial ℂ :=
  ![X ^ 4 * (X - 2), X ^ 2 * (X - 2) * (X - 1), (X - 2) * (X - 1) ^ 2] i

private lemma PsiZ_eq_sum (c : Fin 3 → ℂ) :
    PsiZ c = ∑ i : Fin 3, C (c i) * rnZ i := by
  rw [Fin.sum_univ_three]
  simp [PsiZ, rnZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Summand-wise identity: `c_i · y^{−i}·y'` is the rational function with numerator
`c_i · rnZ i` over `QZ`. -/
private lemma rQc_smul_eq (c : Fin 3 → ℂ) (i : Fin 3) :
    algebraMap ℂ (RatFunc ℂ) (c i) * rQc i
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (C (c i) * rnZ i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ := by
  fin_cases i <;>
    · simp only [rnZ, rQc, yQc, dyQc, QZ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      norm_num
      simp only [map_mul, map_pow, RatFunc.algebraMap_C, map_sub, map_one, map_ofNat]
      field_simp

/-- The right hand side `Σ_i c_i y^{−i} y'` as an explicit rational function `PsiZ c / QZ`. -/
private lemma rhsZ_eq (c : Fin 3 → ℂ) :
    RhsZ c = algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ := by
  rw [RhsZ, Finset.sum_congr rfl (fun i _ => rQc_smul_eq c i), ← Finset.sum_div]
  congr 1
  rw [PsiZ_eq_sum, map_sum]

private lemma rootMult_X_cube (α : ℂ) :
    ((X : Polynomial ℂ) ^ 3).rootMultiplicity α = if α = 0 then 3 else 0 := by
  by_cases h : α = 0
  · subst h
    rw [show (X : Polynomial ℂ) ^ 3 = (X - C (0 : ℂ)) ^ 3 by simp,
      Polynomial.rootMultiplicity_X_sub_C_pow, if_pos rfl]
  · rw [if_neg h, Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    have h2 : α ^ 3 = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at hroot
      exact hroot
    exact h ((pow_eq_zero_iff (by norm_num)).mp h2)

private lemma rootMult_Xsub1_sq (α : ℂ) :
    ((X - C (1 : ℂ)) ^ 2).rootMultiplicity α = if α = 1 then 2 else 0 := by
  by_cases h : α = 1
  · subst h
    rw [Polynomial.rootMultiplicity_X_sub_C_pow, if_pos rfl]
  · rw [if_neg h, Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    have h2 : Polynomial.eval α (X - C (1 : ℂ)) = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_pow] at hroot
      exact (pow_eq_zero_iff (by norm_num)).mp hroot
    have h3 : α - 1 = 0 := by simpa using h2
    exact h (sub_eq_zero.mp h3)

private lemma QZ_eq' : QZ = X ^ 3 * (X - C (1 : ℂ)) ^ 2 := by
  rw [QZ, Polynomial.C_1]

/-- The root multiplicity of the common denominator `QZ = x³(x−1)²`. -/
private lemma rootMult_QZ (α : ℂ) :
    QZ.rootMultiplicity α = if α = 0 then 3 else if α = 1 then 2 else 0 := by
  rw [QZ_eq', Polynomial.rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero 3 Polynomial.X_ne_zero)
        (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero (1 : ℂ)))),
    rootMult_X_cube, rootMult_Xsub1_sq]
  by_cases h1 : α = 1
  · subst h1; simp
  · by_cases h0 : α = 0
    · subst h0; simp [h1]
    · simp [h1, h0]

theorem Zadj_rhs (c : Fin 3 → ℂ) :
    RhsZ c = algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ ∧
      (∀ α : ℂ, (if α = 0 then (-3 : ℤ) else if α = 1 then (-2 : ℤ) else 0)
        ≤ Commons.FieldTheory.RatFunc.ordAtT α (RhsZ c)) := by
  refine ⟨rhsZ_eq c, ?_⟩
  intro α
  rw [rhsZ_eq c]
  rcases eq_or_ne (PsiZ c) 0 with hp | hp
  · rw [hp, map_zero, zero_div]
    simp [Commons.FieldTheory.RatFunc.ordAtT]
  · have hA : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c) ≠ 0 := fun h =>
      hp (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using h))
    have hB : algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ ≠ 0 := fun h =>
      QZ_ne_zero (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using h))
    have hne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiZ c)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) QZ ≠ 0 := div_ne_zero hA hB
    rw [Commons.FieldTheory.RatFunc.ordAtT_def α hne,
      Commons.FieldTheory.RatFunc.ordAt_div α hA hB,
      Commons.FieldTheory.RatFunc.ordAt_algebraMap,
      Commons.FieldTheory.RatFunc.ordAt_algebraMap]
    rw [WithTop.coe_le_coe]
    have hqr : (QZ.rootMultiplicity α : ℤ) = if α = 0 then (3 : ℤ) else if α = 1 then 2 else 0 := by
      rw [rootMult_QZ]
      by_cases h0 : α = 0
      · simp [h0]
      · by_cases h1 : α = 1
        · simp [h0, h1]
        · simp [h0, h1]
    rw [hqr]
    have hnn : (0 : ℤ) ≤ (Polynomial.rootMultiplicity α (PsiZ c) : ℤ) := Int.natCast_nonneg _
    split_ifs <;> omega

end

end Work.A14D
