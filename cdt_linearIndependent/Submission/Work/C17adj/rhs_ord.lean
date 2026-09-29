import Mathlib
import Submission.Work.C17adj.divisor_defs
import Submission.Work.C17adj.rhs_structure

/-!
# Order of vanishing of the right-hand side `Σ_i c_i y^{i−4} y'` at `x = 0` and `x = 1`

With `y = x²/(x−1)` and `y' = x(x−2)/(x−1)²`, the summand `y^{i−4}·y'` equals

`x^{2i}(x−2)(x−1)^{5−i} / (x⁷(x−1)³)`,

so (by `rhs_structure`) the whole right-hand side is `Ψ(c) / x⁷(x−1)³` with `Ψ(c) = PsiNum c`
a polynomial.  Hence its order of vanishing `ordAtT α` is

`rootMultiplicity α Ψ(c) − rootMultiplicity α (x⁷(x−1)³)`,

and since the first term is a natural number while the second equals `3` at `α = 1`, `7` at
`α = 0` and `0` otherwise, the order is bounded below by `−3` at `x = 1`, by `−7` at `x = 0`
and by `0` elsewhere.  These are exactly the exponents of the singularities `x = 1`, `x = 0`
of the adjoint equation.
-/

namespace Work.C17adj

open Polynomial

private lemma rootMult_X_seven (α : ℂ) :
    ((Polynomial.X : Polynomial ℂ) ^ 7).rootMultiplicity α = if α = 0 then 7 else 0 := by
  by_cases h : α = 0
  · subst h
    rw [show (Polynomial.X : Polynomial ℂ) ^ 7 = (Polynomial.X - Polynomial.C (0:ℂ)) ^ 7 by simp,
      Polynomial.rootMultiplicity_X_sub_C_pow, if_pos rfl]
  · rw [if_neg h, Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    have h2 : α ^ 7 = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at hroot
      exact hroot
    exact h ((pow_eq_zero_iff (by norm_num)).mp h2)

private lemma rootMult_Xsub1_cube (α : ℂ) :
    ((Polynomial.X - Polynomial.C (1 : ℂ)) ^ 3).rootMultiplicity α = if α = 1 then 3 else 0 := by
  by_cases h : α = 1
  · subst h
    rw [Polynomial.rootMultiplicity_X_sub_C_pow, if_pos rfl]
  · rw [if_neg h, Polynomial.rootMultiplicity_eq_zero]
    intro hroot
    have h2 : Polynomial.eval α (Polynomial.X - Polynomial.C (1:ℂ)) = 0 := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_pow] at hroot
      exact (pow_eq_zero_iff (by norm_num)).mp hroot
    have h3 : α - 1 = 0 := by simpa using h2
    exact h (sub_eq_zero.mp h3)

/-- The common denominator `x⁷(x−1)³` written with the `C`-form of the numeral. -/
private lemma key_eq : ((Polynomial.X : Polynomial ℂ) ^ 7 * (Polynomial.X - (1 : Polynomial ℂ)) ^ 3)
    = Polynomial.X ^ 7 * (Polynomial.X - Polynomial.C (1:ℂ)) ^ 3 := by
  rw [Polynomial.C_1]

/-- The root multiplicity of the common denominator `x⁷(x−1)³` at `α`. -/
private lemma rootMult_q (α : ℂ) :
    ((Polynomial.X : Polynomial ℂ) ^ 7 * (Polynomial.X - (1 : Polynomial ℂ)) ^ 3).rootMultiplicity α
      = if α = 1 then 3 else if α = 0 then 7 else 0 := by
  rw [key_eq, Polynomial.rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero 7 Polynomial.X_ne_zero)
        (pow_ne_zero 3 (Polynomial.X_sub_C_ne_zero (1:ℂ)))),
    rootMult_X_seven, rootMult_Xsub1_cube]
  by_cases h1 : α = 1
  · subst h1; simp
  · by_cases h0 : α = 0
    · subst h0; simp [h1]
    · simp [h1, h0]

theorem rhs_ord (c : Fin 6 → ℂ) (α : ℂ) :
    (if α = 1 then (-3 : ℤ) else if α = 0 then (-7 : ℤ) else 0)
      ≤ Commons.FieldTheory.RatFunc.ordAtT α (Work.C17adj.RhsC c) := by
  obtain ⟨-, hRhs⟩ := rhs_structure c
  rw [hRhs]
  rcases eq_or_ne (PsiNum c) 0 with hp | hp
  · rw [hp, map_zero, zero_div]
    simp [Commons.FieldTheory.RatFunc.ordAtT]
  · have hA : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiNum c) ≠ 0 := fun h =>
      hp (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using h))
    have hB : algebraMap (Polynomial ℂ) (RatFunc ℂ)
        ((Polynomial.X : Polynomial ℂ) ^ 7 * (Polynomial.X - (1:Polynomial ℂ)) ^ 3) ≠ 0 := fun h =>
      mul_ne_zero (pow_ne_zero 7 Polynomial.X_ne_zero)
        (pow_ne_zero 3 (Polynomial.X_sub_C_ne_zero (1:ℂ)))
        (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using h))
    have hne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (PsiNum c)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
            ((Polynomial.X : Polynomial ℂ) ^ 7 * (Polynomial.X - (1:Polynomial ℂ)) ^ 3) ≠ 0 :=
      div_ne_zero hA hB
    rw [Commons.FieldTheory.RatFunc.ordAtT_def α hne,
      Commons.FieldTheory.RatFunc.ordAt_div α hA hB,
      Commons.FieldTheory.RatFunc.ordAt_algebraMap,
      Commons.FieldTheory.RatFunc.ordAt_algebraMap]
    rw [WithTop.coe_le_coe]
    have hqr : (Polynomial.rootMultiplicity α
        ((Polynomial.X : Polynomial ℂ) ^ 7 * (Polynomial.X - (1:Polynomial ℂ)) ^ 3) : ℤ)
        = if α = 1 then (3:ℤ) else if α = 0 then (7:ℤ) else 0 := by
      by_cases h1 : α = 1
      · subst h1; rw [rootMult_q]; simp
      · by_cases h0 : α = 0
        · subst h0; rw [rootMult_q]; simp [h1]
        · rw [rootMult_q]; simp [h1, h0]
    rw [hqr]
    have hnn : (0:ℤ) ≤ (Polynomial.rootMultiplicity α (PsiNum c) : ℤ) := Int.natCast_nonneg _
    split_ifs <;> omega

end Work.C17adj
