import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

/-!
# Shifted elementary symmetric functions of `y + a_l`

For the pencil lemma `Work.LinnikBurgess.critN_pencil` we need the elementary symmetric
functions of the three numbers `y + a l` (`l : Fin 3`), for a fixed shift `y : ℕ`.
Writing `u = X - y`, the cubic `∏ l, (X + a l)` becomes `u^3 + sh1 · u^2 + sh2 · u + sh3`,
where `sh1, sh2, sh3` are the elementary symmetric functions of `(y + a 0, y + a 1, y + a 2)`;
this is the form in which the Wronskian `critN = f_a' f_b - f_a f_b'` can be evaluated at `y`.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- `(y + a 0) + (y + a 1) + (y + a 2)`. -/
def sh1 (y : ℕ) (a : Fin 3 → ℕ) : ℕ := (y + a 0) + (y + a 1) + (y + a 2)

/-- `∑_{i<j} (y + a i) * (y + a j)`. -/
def sh2 (y : ℕ) (a : Fin 3 → ℕ) : ℕ :=
  (y + a 0) * (y + a 1) + (y + a 0) * (y + a 2) + (y + a 1) * (y + a 2)

/-- `(y + a 0) * (y + a 1) * (y + a 2)`. -/
def sh3 (y : ℕ) (a : Fin 3 → ℕ) : ℕ := (y + a 0) * (y + a 1) * (y + a 2)

/-- The cubic `(X - z)^3 + s1 (X - z)^2 + s2 (X - z) + s3`, written in the shift `z`. -/
noncomputable def cubicIn (z s1 s2 s3 : ℤ) : ℤ[X] :=
  (X - C z) ^ 3 + C s1 * (X - C z) ^ 2 + C s2 * (X - C z) + C s3

/-- Expansion of a product of three linear factors in the shifted variable `X - z`. -/
theorem prod_three_shift (z : ℤ) (v : Fin 3 → ℤ) :
    (∏ l : Fin 3, ((X - C z) + C (v l))) =
      (X - C z) ^ 3 + C (v 0 + v 1 + v 2) * (X - C z) ^ 2
        + C (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) * (X - C z) + C (v 0 * v 1 * v 2) := by
  rw [Fin.prod_univ_three]; simp only [map_add, map_mul]; ring

theorem cubicIn_deriv (z s1 s2 s3 : ℤ) :
    derivative (cubicIn z s1 s2 s3)
      = 3 * (X - C z) ^ 2 + C (2 * s1) * (X - C z) + C s2 := by
  simp only [cubicIn, derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_X,
    derivative_sub, C_mul, C_eq_natCast, map_ofNat]
  ring

theorem cubicIn_deriv2 (z s1 s2 s3 : ℤ) :
    derivative (derivative (cubicIn z s1 s2 s3)) = 6 * (X - C z) + C (2 * s1) := by
  simp only [cubicIn, derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_X,
    derivative_sub, derivative_one, derivative_zero, derivative_natCast, C_mul,
    C_eq_natCast, map_ofNat]
  ring

theorem cubicIn_eval_self (z s1 s2 s3 : ℤ) : (cubicIn z s1 s2 s3).eval z = s3 := by
  simp [cubicIn]

theorem cubicIn_deriv_eval_self (z s1 s2 s3 : ℤ) :
    (derivative (cubicIn z s1 s2 s3)).eval z = s2 := by
  rw [cubicIn_deriv]; simp

theorem cubicIn_deriv2_eval_self (z s1 s2 s3 : ℤ) :
    (derivative (derivative (cubicIn z s1 s2 s3))).eval z = 2 * s1 := by
  rw [cubicIn_deriv2]; simp

/-- `cubicZ a` expanded around the shift `y`, with shifted coefficients `sh1, sh2, sh3`. -/
theorem cubicZ_eq_cubicIn (a : Fin 3 → ℕ) (y : ℕ) :
    cubicZ a = cubicIn (y : ℤ) (sh1 y a) (sh2 y a) (sh3 y a) := by
  have hfac : ∀ l : Fin 3, (X + C (((a l : ℕ) : ℤ)))
      = (X - C (y : ℤ)) + C ((y : ℤ) + ((a l : ℕ) : ℤ)) := by
    intro l; rw [C_add]; ring
  have h1 : ((y : ℤ) + ((a 0 : ℕ) : ℤ)) + ((y : ℤ) + ((a 1 : ℕ) : ℤ))
      + ((y : ℤ) + ((a 2 : ℕ) : ℤ)) = (sh1 y a : ℤ) := by
    simp only [sh1, Nat.cast_add]
  have h2 : ((y : ℤ) + ((a 0 : ℕ) : ℤ)) * ((y : ℤ) + ((a 1 : ℕ) : ℤ))
      + ((y : ℤ) + ((a 0 : ℕ) : ℤ)) * ((y : ℤ) + ((a 2 : ℕ) : ℤ))
      + ((y : ℤ) + ((a 1 : ℕ) : ℤ)) * ((y : ℤ) + ((a 2 : ℕ) : ℤ))
      = (sh2 y a : ℤ) := by
    simp only [sh2, Nat.cast_add, Nat.cast_mul]
  have h3 : ((y : ℤ) + ((a 0 : ℕ) : ℤ)) * ((y : ℤ) + ((a 1 : ℕ) : ℤ))
      * ((y : ℤ) + ((a 2 : ℕ) : ℤ)) = (sh3 y a : ℤ) := by
    simp only [sh3, Nat.cast_add, Nat.cast_mul]
  have step : (∏ l : Fin 3, (X + C (((a l : ℕ) : ℤ))))
      = ∏ l : Fin 3, ((X - C (y : ℤ)) + C ((y : ℤ) + ((a l : ℕ) : ℤ))) :=
    Finset.prod_congr rfl (fun l _ => hfac l)
  rw [cubicZ, step, prod_three_shift, h1, h2, h3, cubicIn]

theorem cubicZ_eval_shift (a : Fin 3 → ℕ) (y : ℕ) :
    (cubicZ a).eval (y : ℤ) = (sh3 y a : ℤ) := by
  rw [cubicZ_eq_cubicIn, cubicIn_eval_self]

theorem cubicZ_deriv_eval_shift (a : Fin 3 → ℕ) (y : ℕ) :
    (derivative (cubicZ a)).eval (y : ℤ) = (sh2 y a : ℤ) := by
  rw [cubicZ_eq_cubicIn, cubicIn_deriv_eval_self]

theorem cubicZ_deriv2_eval_shift (a : Fin 3 → ℕ) (y : ℕ) :
    (derivative (derivative (cubicZ a))).eval (y : ℤ) = 2 * (sh1 y a : ℤ) := by
  rw [cubicZ_eq_cubicIn, cubicIn_deriv2_eval_self]

/-- `critN` evaluated at the critical point `y`. -/
theorem critN_eval_shift (a b : Fin 3 → ℕ) (y : ℕ) :
    (critN a b).eval (y : ℤ)
      = (sh2 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh2 y b : ℤ) := by
  simp only [critN, eval_sub, eval_mul, cubicZ_eval_shift, cubicZ_deriv_eval_shift]

/-- The derivative of `critN` evaluated at the critical point `y`. -/
theorem critN_deriv_eval_shift (a b : Fin 3 → ℕ) (y : ℕ) :
    (derivative (critN a b)).eval (y : ℤ)
      = 2 * ((sh1 y a : ℤ) * (sh3 y b : ℤ) - (sh3 y a : ℤ) * (sh1 y b : ℤ)) := by
  simp only [critN, derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul,
    cubicZ_eval_shift, cubicZ_deriv_eval_shift, cubicZ_deriv2_eval_shift]
  ring

/-- Casting a natural number through `ℤ` and `Int.castRingHom`. -/
lemma castRingHom_natCast (N n : ℕ) :
    (Int.castRingHom (ZMod N)) ((n : ℕ) : ℤ) = ((n : ℕ) : ZMod N) := by
  simp

/-- `cubicZ a` reduced mod `N` and expanded around the shift `y`. -/
theorem cubicZ_map_eq_prod_shift (a : Fin 3 → ℕ) (y N : ℕ) :
    (cubicZ a).map (Int.castRingHom (ZMod N))
      = ∏ l : Fin 3, ((X - C (y : ZMod N)) + C ((y : ZMod N) + ((a l : ℕ) : ZMod N))) := by
  rw [cubicZ, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, castRingHom_natCast N (a l), C_add]
  ring

/-- The shifted first elementary symmetric function, in the `r`-form used by
`critN_pencil_alg`. -/
theorem sh1_cast_eq {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y : R) + (a 0 : R)) + ((y : R) + (a 1 : R)) + ((y : R) + (a 2 : R)) = (sh1 y a : R) := by
  simp only [sh1, Nat.cast_add]

/-- The shifted second elementary symmetric function, in the `r`-form. -/
theorem sh2_cast_eq {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y : R) + (a 0 : R)) * ((y : R) + (a 1 : R)) + ((y : R) + (a 0 : R)) * ((y : R) + (a 2 : R))
      + ((y : R) + (a 1 : R)) * ((y : R) + (a 2 : R)) = (sh2 y a : R) := by
  simp only [sh2, Nat.cast_add, Nat.cast_mul]

/-- The shifted third elementary symmetric function, in the `r`-form. -/
theorem sh3_cast_eq {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y : R) + (a 0 : R)) * ((y : R) + (a 1 : R)) * ((y : R) + (a 2 : R)) = (sh3 y a : R) := by
  simp only [sh3, Nat.cast_add, Nat.cast_mul]

end Work.LinnikBurgess
