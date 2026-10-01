import Mathlib
import Submission.Work.LinnikBurgess.fcd_aux
import Submission.Work.LinnikBurgess.critN_pencil

/-!
# The frame step at a single prime

Local computation for the multi-prime frame step.  Fix a prime `p`, an exponent `k` and a frame
`(a0, a1, b)`.  This file proves that the `a2` admissible at level `p ^ k` for the frame lie in at
most three residue classes modulo `p ^ (max 0 (k - v_p 2 - v_p (a0 - a1)))`, split into the two
cases distinguished by whether `p ^ (k - v_p 2)` divides `∏_l (b_l - a0)`.
-/

set_option linter.unusedVariables false

open scoped BigOperators
open Finset

namespace Work.LinnikBurgess

open Polynomial

/-- Explicit shape of the cubic `cubicZ a = ∏_l (X + a_l)`. -/
theorem fcd_cubicZ_eq_expand (a : Fin 3 → ℕ) :
    cubicZ a = X ^ 3 + C (esymm3 a 0) * X ^ 2 + C (esymm3 a 1) * X + C (esymm3 a 2) := by
  rw [cubicZ, Fin.prod_univ_three]
  simp [esymm3]
  ring

/-- The `X ^ 2`-coefficient of that shape. -/
theorem fcd_coeff_two_cubic {c0 c1 c2 : ℤ} :
    (X ^ 3 + C c0 * X ^ 2 + C c1 * X + C c2 : ℤ[X]).coeff 2 = c0 := by
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num

/-- The `X ^ 2` coefficient of `cubicZ a` is the first elementary symmetric function. -/
theorem fcd_cubicZ_coeff_two (a : Fin 3 → ℕ) : (cubicZ a).coeff 2 = esymm3 a 0 := by
  rw [fcd_cubicZ_eq_expand, fcd_coeff_two_cubic]

/-- `esymm3 a 0` is the sum of the three entries. -/
theorem fcd_esymm3_zero (a : Fin 3 → ℕ) :
    esymm3 a 0 = (a 0 : ℤ) + (a 1 : ℤ) + (a 2 : ℤ) := by
  simp [esymm3]

/-- Evaluating the reduction of `cubicZ a` modulo `N` at a point `z`. -/
theorem fcd_eval_cubicZ_map (a : Fin 3 → ℕ) (N : ℕ) (z : ZMod N) :
    Polynomial.eval z ((cubicZ a).map (Int.castRingHom (ZMod N)))
      = ∏ l : Fin 3, (z + ((a l : ℕ) : ZMod N)) := by
  rw [cubicZ, Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, castRingHom_natCast]
  simp

/-- The reduction of `cubicZ a` modulo `N` vanishes at `-(a i)`. -/
theorem fcd_eval_cubicZ_map_self (a : Fin 3 → ℕ) (N : ℕ) (i : Fin 3) :
    Polynomial.eval (-(((a i : ℕ) : ℤ) : ZMod N))
      ((cubicZ a).map (Int.castRingHom (ZMod N))) = 0 := by
  rw [fcd_eval_cubicZ_map]
  refine Finset.prod_eq_zero (s := Finset.univ) (i := i) (Finset.mem_univ i) ?_
  simp

/-- An integer not divisible by a prime `p` is a unit modulo `p ^ K`. -/
theorem fcd_isUnit_natCast_zmod_of_not_dvd {p K m : ℕ} [Fact p.Prime] (h : ¬ p ∣ m) :
    IsUnit ((m : ℕ) : ZMod (p ^ K)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (Fact.out : p.Prime).coprime_pow_of_not_dvd h

/-- **Frame step, degenerate case.**  If `p ^ (k - v_p 2)` divides `f_b(-a0) = ∏_l (b_l - a0)`,
then every `a2` admissible for the frame at level `p ^ k` satisfies
`a2 ≡ e₁(b) - a0 - a1 (mod p ^ (k - v_p 2))`. -/
theorem fcd_frame_class_pow_dvd {p k : ℕ} [Fact p.Prime] (a0 a1 : ℕ) (b : Fin 3 → ℕ)
    (h01 : a0 ≠ a1) (hb : ∀ l : Fin 3, a1 ≠ b l)
    (hAi : ((p ^ (k - padicValNat p 2) : ℕ) : ℤ) ∣ ∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ)))
    {a2 : ℕ} (ha2 : fcd_frameAdm p k a0 a1 b a2) :
    (a2 : ZMod (p ^ (k - padicValNat p 2)))
      = (((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
          : ZMod (p ^ (k - padicValNat p 2))) := by
  obtain ⟨y, hy, hN, hN'⟩ := ha2
  set K := k - padicValNat p 2 with hK
  obtain ⟨c, hcunit, hpencil⟩ := critN_pencil (p := p) (k := k) ![a0, a1, a2] b y hy hN hN'
  -- Evaluate the pencil identity at `X = -a0`, where the `a`-cubic vanishes
  have hev := congrArg (fun Q : Polynomial (ZMod (p ^ K)) =>
    Polynomial.eval (-(a0 : ZMod (p ^ K))) Q) hpencil
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X] at hev
  have hL : Polynomial.eval (-(a0 : ZMod (p ^ K)))
      ((cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ K)))) = 0 := by
    have h := fcd_eval_cubicZ_map_self ![a0, a1, a2] (p ^ K) 0
    simpa using h
  have hb0 : (∏ l : Fin 3, (-(a0 : ZMod (p ^ K)) + ((b l : ℕ) : ZMod (p ^ K)))) = 0 := by
    have hcast : ((∏ l : Fin 3, ((b l : ℤ) - (a0 : ℤ)) : ℤ) : ZMod (p ^ K)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using hAi
    rw [← hcast]
    push_cast
    refine Finset.prod_congr rfl (fun l _ => ?_)
    ring
  have hR : Polynomial.eval (-(a0 : ZMod (p ^ K)))
      ((cubicZ b).map (Int.castRingHom (ZMod (p ^ K)))) = 0 := by
    rw [fcd_eval_cubicZ_map]
    exact hb0
  rw [hL, hR, mul_zero, zero_add] at hev
  -- the second factor is a unit, so `1 - c = 0`
  have hunit : IsUnit ((-(a0 : ZMod (p ^ K)) - (y : ZMod (p ^ K))) ^ 3) := by
    have h1 : IsUnit (((y + a0 : ℕ)) : ZMod (p ^ K)) :=
      fcd_isUnit_natCast_zmod_of_not_dvd (p := p) (K := K) (hy 0).1
    have h2 : (-(a0 : ZMod (p ^ K)) - (y : ZMod (p ^ K)))
        = -(((y + a0 : ℕ)) : ZMod (p ^ K)) := by push_cast; ring
    rw [h2]
    exact (h1.neg).pow 3
  have hc1 : c = 1 := by
    have hz : (1 - c) * ((-(a0 : ZMod (p ^ K)) - (y : ZMod (p ^ K))) ^ 3) = 0 := hev.symm
    exact (sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hunit).mp hz)).symm
  -- Comparing `X ^ 2` coefficients of `cubicZ ![a0,a1,a2]` and `cubicZ b`
  have hp : (cubicZ ![a0, a1, a2]).map (Int.castRingHom (ZMod (p ^ K)))
      = (cubicZ b).map (Int.castRingHom (ZMod (p ^ K))) := by
    have h := hpencil
    rw [hc1] at h
    simpa using h
  have hcoeff := congrArg (fun Q : Polynomial (ZMod (p ^ K)) => Q.coeff 2) hp
  rw [Polynomial.coeff_map, Polynomial.coeff_map, fcd_cubicZ_coeff_two, fcd_cubicZ_coeff_two]
    at hcoeff
  have hsum : ((a0 : ZMod (p ^ K)) + (a1 : ZMod (p ^ K)) + (a2 : ZMod (p ^ K)))
      = ((b 0 : ZMod (p ^ K)) + (b 1 : ZMod (p ^ K)) + (b 2 : ZMod (p ^ K))) := by
    have h := hcoeff
    simp only [fcd_esymm3_zero] at h
    push_cast at h
    simpa using h
  have h : ((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ) - (a0 : ℤ) - (a1 : ℤ) : ℤ)
      = ((b 0 : ℤ) + (b 1 : ℤ) + (b 2 : ℤ)) - ((a0 : ℤ) + (a1 : ℤ)) := by ring
  rw [h]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
  linear_combination hsum

end Work.LinnikBurgess
