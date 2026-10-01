import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_shifts

namespace Work.LinnikBurgess

open Polynomial

/-- **The algebraic heart (linear form).**  Let `u0 u1 u2` be three elements of a commutative ring,
each a right inverse of its own inverse (`u * u⁻¹ = 1`).  Then the sum of the inverses, cleared of
denominators by the product `u0 u1 u2`, is the second elementary symmetric function:
`(Σ u_l⁻¹)·(u0u1u2) = e2`. -/
lemma three_inv_mul_prod {R : Type*} [CommRing R] [Inv R] (u0 u1 u2 : R)
    (h0 : u0 * u0⁻¹ = 1) (h1 : u1 * u1⁻¹ = 1) (h2 : u2 * u2⁻¹ = 1) :
    (u0⁻¹ + u1⁻¹ + u2⁻¹) * (u0 * u1 * u2) = u0 * u1 + u0 * u2 + u1 * u2 := by
  have c0 : u0⁻¹ * u0 = 1 := by rw [mul_comm, h0]
  have c1 : u1⁻¹ * u1 = 1 := by rw [mul_comm, h1]
  have c2 : u2⁻¹ * u2 = 1 := by rw [mul_comm, h2]
  have e0 : u0⁻¹ * (u0 * u1 * u2) = u1 * u2 := by
    rw [show u0⁻¹ * (u0 * u1 * u2) = (u0⁻¹ * u0) * (u1 * u2) by ring, c0, one_mul]
  have e1 : u1⁻¹ * (u0 * u1 * u2) = u0 * u2 := by
    rw [show u1⁻¹ * (u0 * u1 * u2) = (u1⁻¹ * u1) * (u0 * u2) by ring, c1, one_mul]
  have e2 : u2⁻¹ * (u0 * u1 * u2) = u0 * u1 := by
    rw [show u2⁻¹ * (u0 * u1 * u2) = (u2⁻¹ * u2) * (u0 * u1) by ring, c2, one_mul]
  rw [show (u0⁻¹ + u1⁻¹ + u2⁻¹) * (u0 * u1 * u2)
      = u0⁻¹ * (u0 * u1 * u2) + u1⁻¹ * (u0 * u1 * u2) + u2⁻¹ * (u0 * u1 * u2) by ring,
    e0, e1, e2]
  ring

/-- **The algebraic heart (quadratic form).**  Let `u0 u1 u2` be three elements of a commutative
ring, each a right inverse of its own inverse (`u * u⁻¹ = 1`).  Then the product of the sum of the
squares of the inverses with the square of the product `u0 u1 u2` is the square of the second
elementary symmetric function minus `2` times the product of the first and third:
`(Σ u_l⁻²)·(u0u1u2)² = e2² - 2·e1·e3`. -/
lemma three_inv_sq_mul_prod_sq {R : Type*} [CommRing R] [Inv R] (u0 u1 u2 : R)
    (h0 : u0 * u0⁻¹ = 1) (h1 : u1 * u1⁻¹ = 1) (h2 : u2 * u2⁻¹ = 1) :
    (u0⁻¹ ^ 2 + u1⁻¹ ^ 2 + u2⁻¹ ^ 2) * (u0 * u1 * u2) ^ 2
      = (u0 * u1 + u0 * u2 + u1 * u2) ^ 2 - 2 * (u0 + u1 + u2) * (u0 * u1 * u2) := by
  have c0 : u0⁻¹ * u0 = 1 := by rw [mul_comm, h0]
  have c1 : u1⁻¹ * u1 = 1 := by rw [mul_comm, h1]
  have c2 : u2⁻¹ * u2 = 1 := by rw [mul_comm, h2]
  have t0 : u0⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u1 * u2) ^ 2 := by
    have e : u0⁻¹ * (u0 * u1 * u2) = u1 * u2 := by
      rw [show u0⁻¹ * (u0 * u1 * u2) = (u0⁻¹ * u0) * (u1 * u2) by ring, c0, one_mul]
    rw [show u0⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u0⁻¹ * (u0 * u1 * u2)) ^ 2 by ring, e]
  have t1 : u1⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u0 * u2) ^ 2 := by
    have e : u1⁻¹ * (u0 * u1 * u2) = u0 * u2 := by
      rw [show u1⁻¹ * (u0 * u1 * u2) = (u1⁻¹ * u1) * (u0 * u2) by ring, c1, one_mul]
    rw [show u1⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u1⁻¹ * (u0 * u1 * u2)) ^ 2 by ring, e]
  have t2 : u2⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u0 * u1) ^ 2 := by
    have e : u2⁻¹ * (u0 * u1 * u2) = u0 * u1 := by
      rw [show u2⁻¹ * (u0 * u1 * u2) = (u2⁻¹ * u2) * (u0 * u1) by ring, c2, one_mul]
    rw [show u2⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 = (u2⁻¹ * (u0 * u1 * u2)) ^ 2 by ring, e]
  rw [show (u0⁻¹ ^ 2 + u1⁻¹ ^ 2 + u2⁻¹ ^ 2) * (u0 * u1 * u2) ^ 2
      = u0⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 + u1⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2
        + u2⁻¹ ^ 2 * (u0 * u1 * u2) ^ 2 by ring, t0, t1, t2]
  ring

/-- The shifted first elementary symmetric function, in the form matching the raw casts
`((y + a l : ℕ) : R)`. -/
lemma sh1_cast_nat {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y + a 0 : ℕ) : R) + ((y + a 1 : ℕ) : R) + ((y + a 2 : ℕ) : R) = (sh1 y a : R) := by
  simp only [sh1, Nat.cast_add]

/-- The shifted second elementary symmetric function, in the form matching the raw casts. -/
lemma sh2_cast_nat {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y + a 0 : ℕ) : R) * ((y + a 1 : ℕ) : R) + ((y + a 0 : ℕ) : R) * ((y + a 2 : ℕ) : R)
      + ((y + a 1 : ℕ) : R) * ((y + a 2 : ℕ) : R) = (sh2 y a : R) := by
  simp only [sh2, Nat.cast_add, Nat.cast_mul]

/-- The shifted third elementary symmetric function, in the form matching the raw casts. -/
lemma sh3_cast_nat {R : Type*} [CommRing R] (y : ℕ) (a : Fin 3 → ℕ) :
    ((y + a 0 : ℕ) : R) * ((y + a 1 : ℕ) : R) * ((y + a 2 : ℕ) : R) = (sh3 y a : R) := by
  simp only [sh3, Nat.cast_add, Nat.cast_mul]

/-- If the prime `p` does not divide `n`, then `n` is a unit of `ZMod (p ^ e)`, i.e.
`(n : ZMod (p ^ e)) * (n : ZMod (p ^ e))⁻¹ = 1`. -/
lemma zmod_coe_mul_inv_eq_one {p e : ℕ} [Fact p.Prime] {n : ℕ} (hn : ¬ p ∣ n) :
    (((n : ℕ) : ZMod (p ^ e))) * ((((n : ℕ) : ZMod (p ^ e))))⁻¹ = 1 :=
  ZMod.coe_mul_inv_eq_one n
    (Nat.Coprime.pow_right e (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hn).symm)

/-- **Sum of inverses.**  If none of the `y + v l` is divisible by the prime `p`, each of them is a
unit in `ZMod (p ^ e)` and the sum of the inverses, cleared of denominators by the product
`(y+v_0)(y+v_1)(y+v_2)`, equals the second elementary symmetric function:
`(Σ_l (y + v_l)⁻¹) · (y+v_0)(y+v_1)(y+v_2) = Σ_{i<j} (y+v_i)(y+v_j)`. -/
lemma sum_inv_mul_sh3_eq_sh2 {p e : ℕ} [Fact p.Prime] (v : Fin 3 → ℕ) {y : ℕ}
    (hv : ∀ l : Fin 3, ¬ p ∣ y + v l) :
    (∑ l : Fin 3, ((((y + v l : ℕ) : ZMod (p ^ e)))⁻¹))
        * ((sh3 y v : ℕ) : ZMod (p ^ e))
      = ((sh2 y v : ℕ) : ZMod (p ^ e)) := by
  have hunit : ∀ l : Fin 3,
      ((((y + v l : ℕ) : ZMod (p ^ e)))) * ((((y + v l : ℕ) : ZMod (p ^ e))))⁻¹ = 1 :=
    fun l => zmod_coe_mul_inv_eq_one (hv l)
  have h := three_inv_mul_prod (((y + v 0 : ℕ) : ZMod (p ^ e)))
      (((y + v 1 : ℕ) : ZMod (p ^ e))) (((y + v 2 : ℕ) : ZMod (p ^ e)))
      (hunit 0) (hunit 1) (hunit 2)
  rw [Fin.sum_univ_three, ← sh3_cast_nat (R := ZMod (p ^ e)) y v,
    ← sh2_cast_nat (R := ZMod (p ^ e)) y v]
  exact h

/-- **Sum of squared inverses.**  If none of the `y + v l` is divisible by the prime `p`, then each
of them is a unit in `ZMod (p ^ e)` and
`(Σ_l (y + v_l)⁻²) · (y + v_0)(y + v_1)(y + v_2)² = e₂² - 2 e₁ e₃`,
where `e_i = sh i y v` are the (shifted) elementary symmetric functions of the three numbers
`y + v_l`. -/
lemma sum_inv_sq_mul_sh3_sq {p e : ℕ} [Fact p.Prime] (v : Fin 3 → ℕ) {y : ℕ}
    (hv : ∀ l : Fin 3, ¬ p ∣ y + v l) :
    (∑ l : Fin 3, ((((y + v l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
        * ((sh3 y v : ℕ) : ZMod (p ^ e)) ^ 2
      = ((sh2 y v : ℕ) : ZMod (p ^ e)) ^ 2
        - 2 * ((sh1 y v : ℕ) : ZMod (p ^ e)) * ((sh3 y v : ℕ) : ZMod (p ^ e)) := by
  have hunit : ∀ l : Fin 3,
      ((((y + v l : ℕ) : ZMod (p ^ e)))) * ((((y + v l : ℕ) : ZMod (p ^ e))))⁻¹ = 1 :=
    fun l => zmod_coe_mul_inv_eq_one (hv l)
  have h := three_inv_sq_mul_prod_sq (((y + v 0 : ℕ) : ZMod (p ^ e)))
      (((y + v 1 : ℕ) : ZMod (p ^ e))) (((y + v 2 : ℕ) : ZMod (p ^ e)))
      (hunit 0) (hunit 1) (hunit 2)
  rw [Fin.sum_univ_three, ← sh3_cast_nat (R := ZMod (p ^ e)) y v,
    ← sh2_cast_nat (R := ZMod (p ^ e)) y v, ← sh1_cast_nat (R := ZMod (p ^ e)) y v]
  exact h

/-- In `ZMod (p ^ e)`, the second defect of Lemma A is `-D₁'`, cleared of inverses:
`D₂(y) · (f_a(y) f_b(y))² = -N'(y) · f_a(y) f_b(y) + N(y) · (f_a' f_b + f_a f_b')(y)`, with
`N = critN a b` and `y` a unit at `p`.

Hints: with `A_i = sh i y a` and `B_i = sh i y b`, `Uval y a b = A_3 B_3`, `Wval y a b = A_2 B_3 + A_3 B_2`,
`N(y) = A_2 B_3 - A_3 B_2` and `N'(y) = 2 (A_1 B_3 - A_3 B_1)` (`critN_eval_shift`,
`critN_deriv_eval_shift`). Using `∑_l (y+a_l)⁻¹ = A_2/A_3` (units: `ZMod.inv_coe_unit`) and
`∑_l (y+a_l)⁻² = (A_2^2 - 2 A_1 A_3)/A_3^2`, the claim reduces to the `ring` identity
`(A_2²-2A_1A_3)B_3² - (B_2²-2B_1B_3)A_3² = -2(A_1B_3-A_3B_1)A_3B_3 + (A_2B_3-A_3B_2)(A_2B_3+A_3B_2)`. -/
theorem defect2_mul_Uval_sq {p e : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : UnitAt p y a b) :
    defect2 p e a b y * ((((Uval y a b : ℕ)) : ZMod (p ^ e))) ^ 2
      = - ((((critN a b).derivative.eval (y : ℤ) : ℤ)) : ZMod (p ^ e))
            * ((((Uval y a b : ℕ)) : ZMod (p ^ e)))
        + ((((critN a b).eval (y : ℤ) : ℤ)) : ZMod (p ^ e))
            * ((((Wval y a b : ℕ)) : ZMod (p ^ e))) := by
  have hya : ∀ l : Fin 3, ¬ p ∣ y + a l := fun l => (hy l).1
  have hyb : ∀ l : Fin 3, ¬ p ∣ y + b l := fun l => (hy l).2
  have hA := sum_inv_sq_mul_sh3_sq (p := p) (e := e) a hya
  have hB := sum_inv_sq_mul_sh3_sq (p := p) (e := e) b hyb
  -- `defect2` is the difference of the two sums of squared inverses
  have hD : defect2 p e a b y
      = (∑ l : Fin 3, ((((y + a l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
        - ∑ l : Fin 3, ((((y + b l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2 := rfl
  -- the values and derivatives of the two cubics at `y`, in shifted form
  have hU : ((((Uval y a b : ℕ)) : ZMod (p ^ e)))
      = ((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e)) := by
    rw [Uval]; push_cast; ring
  have hW : ((((Wval y a b : ℕ)) : ZMod (p ^ e)))
      = ((sh2 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e))
        + ((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh2 y b : ℕ) : ZMod (p ^ e)) := by
    rw [Wval]; push_cast; ring
  have hN : ((((critN a b).eval (y : ℤ) : ℤ)) : ZMod (p ^ e))
      = ((sh2 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e))
        - ((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh2 y b : ℕ) : ZMod (p ^ e)) := by
    rw [critN_eval_shift]; push_cast; ring
  have hN' : ((((critN a b).derivative.eval (y : ℤ) : ℤ)) : ZMod (p ^ e))
      = 2 * (((sh1 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e))
        - ((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh1 y b : ℕ) : ZMod (p ^ e))) := by
    rw [critN_deriv_eval_shift]; push_cast; ring
  rw [hD, hU, hW, hN, hN']
  conv_lhs =>
    rw [show
      ((∑ l : Fin 3, ((((y + a l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
          - ∑ l : Fin 3, ((((y + b l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
        * (((sh3 y a : ℕ) : ZMod (p ^ e)) * ((sh3 y b : ℕ) : ZMod (p ^ e))) ^ 2
      = ((∑ l : Fin 3, ((((y + a l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
            * ((sh3 y a : ℕ) : ZMod (p ^ e)) ^ 2) * ((sh3 y b : ℕ) : ZMod (p ^ e)) ^ 2
        - ((∑ l : Fin 3, ((((y + b l : ℕ) : ZMod (p ^ e)))⁻¹) ^ 2)
            * ((sh3 y b : ℕ) : ZMod (p ^ e)) ^ 2) * ((sh3 y a : ℕ) : ZMod (p ^ e)) ^ 2
      by ring]
  rw [hA, hB]
  ring

end Work.LinnikBurgess
