import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Work.A7.analyticOrderNatAt_star_symm
import Submission.Work.A7.completedHurwitzZetaEven_entire_star

namespace Work.A7

open Complex

variable {n : ℕ} [NeZero n]

/-- Conjugation commutes with complex powers of a positive natural number. -/
private lemma star_natCast_cpow (n : ℕ) [NeZero n] (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-((starRingEnd ℂ) s))) = (n : ℂ) ^ (-s) := by
  rw [← Complex.ofReal_natCast]
  rw [Commons.NumberTheory.DirichletCharacter.conj_cpow_ofReal_pos n
    (Nat.cast_pos.mpr (NeZero.pos n)) (-((starRingEnd ℂ) s))]
  rw [map_neg, starRingEnd_apply, starRingEnd_apply, star_star]

/-- **Schwarz reflection for the completed even Hurwitz zeta function.** -/
theorem completedHurwitzZetaEven_star (a : UnitAddCircle) (s : ℂ) :
    (starRingEnd ℂ) (HurwitzZeta.completedHurwitzZetaEven a ((starRingEnd ℂ) s)) =
      HurwitzZeta.completedHurwitzZetaEven a s := by
  have h1 : (starRingEnd ℂ) ((if a = 0 then (1 : ℂ) else 0) / ((starRingEnd ℂ) s)) =
      (if a = 0 then (1 : ℂ) else 0) / s := by
    rw [map_div₀, apply_ite (starRingEnd ℂ), map_one, map_zero]
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  have h2 : (starRingEnd ℂ) (1 / (1 - ((starRingEnd ℂ) s))) = 1 / (1 - s) := by
    rw [map_div₀, map_one, map_sub, map_one]
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  rw [HurwitzZeta.completedHurwitzZetaEven_eq a ((starRingEnd ℂ) s), map_sub, map_sub,
    completedHurwitzZetaEven_entire_star a s, h1, h2,
    ← HurwitzZeta.completedHurwitzZetaEven_eq a s]

/-- The trivial character modulo `n` is even. -/
lemma trivialChar_functionEven (n : ℕ) [NeZero n] :
    Function.Even (fun j : ZMod n => (1 : DirichletCharacter ℂ n) j) :=
  DirichletCharacter.Even.to_fun (by
    show (1 : DirichletCharacter ℂ n) (-1) = 1
    rw [MulChar.one_apply (isUnit_one.neg)])

/-- The trivial character modulo `n` is conjugation-invariant. -/
lemma trivialChar_apply_star (n : ℕ) [NeZero n] (j : ZMod n) :
    (starRingEnd ℂ) ((1 : DirichletCharacter ℂ n) j) = (1 : DirichletCharacter ℂ n) j := by
  by_cases hj : IsUnit j
  · rw [MulChar.one_apply hj]; simp
  · rw [MulChar.map_nonunit _ hj]; simp

/-- **Schwarz reflection for the completed L-function of the trivial character.** -/
theorem trivialChar_completedLFunction_star (n : ℕ) [NeZero n] (s : ℂ) :
    (starRingEnd ℂ)
        (DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n) ((starRingEnd ℂ) s)) =
      DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n) s := by
  have heven := trivialChar_functionEven n
  have hstar := trivialChar_apply_star n
  rw [show DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n) ((starRingEnd ℂ) s) =
        ZMod.completedLFunction (fun j : ZMod n => (1 : DirichletCharacter ℂ n) j)
          ((starRingEnd ℂ) s) from rfl,
      show DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n) s =
        ZMod.completedLFunction (fun j : ZMod n => (1 : DirichletCharacter ℂ n) j) s from rfl,
      ZMod.completedLFunction_def_even heven ((starRingEnd ℂ) s),
      ZMod.completedLFunction_def_even heven s]
  rw [map_mul, map_sum, star_natCast_cpow n s]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hstar j, completedHurwitzZetaEven_star (ZMod.toAddCircle j) s]

/-- The requested lemma. -/
theorem trivialChar_completedLFunction_conj_order {n : ℕ} [NeZero n] (ρ : ℂ) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n)) ((starRingEnd ℂ) ρ)
      = analyticOrderNatAt (DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ n)) ρ := by
  exact analyticOrderNatAt_star_symm _ (fun s => trivialChar_completedLFunction_star n s) ρ

end Work.A7
