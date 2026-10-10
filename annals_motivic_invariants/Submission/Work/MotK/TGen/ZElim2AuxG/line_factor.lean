import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The linear factor of `g0p r`

`Work.MotK.TGen.g0p r` is the normalised `μ₅`-invariant quintic
`r^7 X 0^5 - r^3(3+r^5) X 0^2 X 1 + (1+2r^5) X 0 X 1^3 - r^2 X 1^5 + r^2`.
This file proves that a linear factor `c X 0 + d X 1 + e` of it forces `(r*d)^5 = -c^5`.

The argument: the line `c X 0 + d X 1 + e = 0` is parametrised by
`X 0 = -(d/c) X - (e/c)`, `X 1 = X` (using `c ≠ 0`), so substituting it into the factorisation
kills the linear factor and shows that the substituted `g0p r` vanishes.  Reading off the
coefficient of `X^5` (the top degree, where only `r^7 X 0^5` and `-r^2 X 1^5` contribute) gives
`r^7 (-(d/c))^5 - r^2 = 0`, which after multiplying by `c^5` is `r^5 d^5 = -c^5`.
-/

set_option maxHeartbeats 1000000

open Polynomial

namespace Work.MotK.TGen.ZElim2AuxG

variable {L : Type*} [Field L]

/-- The `L`-algebra map sending `X 0 ↦ -(d/c) X - (e/c)` and `X 1 ↦ X`, i.e. the parameterisation
of the line `c X 0 + d X 1 + e = 0` (recall `c ≠ 0`). -/
noncomputable def phiSub (c d e : L) : MvPolynomial (Fin 2) L →ₐ[L] Polynomial L :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then C (-(d / c)) * X + C (-(e / c)) else X)

lemma phiSub_X0 (c d e : L) :
    phiSub c d e (MvPolynomial.X 0) = C (-(d / c)) * X + C (-(e / c)) := by
  simp [phiSub]

lemma phiSub_X1 (c d e : L) : phiSub c d e (MvPolynomial.X 1) = X := by
  simp [phiSub]

lemma phiSub_C (c d e x : L) : phiSub c d e (MvPolynomial.C x) = C x := by
  simp [phiSub]

/-- The coefficient of `X ^ n` in `(C a * X + C b) ^ n` is `a ^ n`. -/
lemma coeff_linear_pow_self (a b : L) (n : ℕ) :
    coeff ((C a * X + C b) ^ n) n = a ^ n := by
  by_cases ha : a = 0
  · subst ha
    have hsimp : (C (0 : L) * X + C b : Polynomial L) = C b := by simp
    rw [hsimp, ← C_pow, coeff_C]
    rcases n with _ | n <;> simp
  · have hfac : (C a * X + C b : Polynomial L) = C a * (X + C (a⁻¹ * b)) := by
      rw [mul_add, ← C_mul, show a * (a⁻¹ * b) = b from by
          rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]]
    rw [hfac, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow, tsub_self, pow_zero,
      Nat.choose_self, Nat.cast_one, mul_one, mul_one]

lemma natDegree_lin_le (a b : L) :
    (C a * X + C b : Polynomial L).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · calc (C a * X : Polynomial L).natDegree ≤ (X : Polynomial L).natDegree :=
        Polynomial.natDegree_C_mul_le a X
      _ = 1 := Polynomial.natDegree_X
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1

lemma natDegree_sq_mul_X_le (a b : L) :
    ((C a * X + C b : Polynomial L) ^ 2 * X).natDegree ≤ 3 := by
  have hF : (C a * X + C b : Polynomial L).natDegree ≤ 1 := natDegree_lin_le a b
  calc ((C a * X + C b : Polynomial L) ^ 2 * X).natDegree
      ≤ ((C a * X + C b : Polynomial L) ^ 2).natDegree + (X : Polynomial L).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 2 * (C a * X + C b : Polynomial L).natDegree + 1 := by
        rw [Polynomial.natDegree_X]
        have := Polynomial.natDegree_pow_le (p := (C a * X + C b : Polynomial L)) (n := 2)
        omega
    _ ≤ 2 * 1 + 1 := by
        have := Nat.mul_le_mul_left 2 hF
        omega
    _ = 3 := by norm_num

lemma natDegree_mul_X3_le (a b : L) :
    ((C a * X + C b : Polynomial L) * X ^ 3).natDegree ≤ 4 := by
  have hF : (C a * X + C b : Polynomial L).natDegree ≤ 1 := natDegree_lin_le a b
  have hX3 : (X ^ 3 : Polynomial L).natDegree ≤ 3 := by
    calc (X ^ 3 : Polynomial L).natDegree ≤ 3 * (X : Polynomial L).natDegree :=
          Polynomial.natDegree_pow_le
      _ = 3 := by rw [Polynomial.natDegree_X, mul_one]
  calc ((C a * X + C b : Polynomial L) * X ^ 3).natDegree
      ≤ (C a * X + C b : Polynomial L).natDegree + (X ^ 3 : Polynomial L).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 1 + 3 := add_le_add hF hX3
    _ = 4 := by norm_num

lemma coeff_sq_mul_X (a b : L) :
    coeff ((C a * X + C b : Polynomial L) ^ 2 * X) 5 = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt (natDegree_sq_mul_X_le a b) (by norm_num)

lemma coeff_mul_X3 (a b : L) :
    coeff ((C a * X + C b : Polynomial L) * X ^ 3) 5 = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt (natDegree_mul_X3_le a b) (by norm_num)

lemma coeff_C_eq_zero (x : L) : coeff (C x : Polynomial L) 5 = 0 := by
  rw [Polynomial.coeff_C]; simp

theorem line_factor {L : Type*} [Field L] (r c d e : L) (hr : r ≠ 0) (hc : c ≠ 0)
    (H : MvPolynomial (Fin 2) L)
    (h : (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
        + MvPolynomial.C e) * H = Work.MotK.TGen.g0p r) :
    (r * d) ^ 5 = -c ^ 5 := by
  have hcd' : c * (d / c) = d := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm c d, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have hce' : c * (e / c) = e := by
    rw [div_eq_mul_inv, ← mul_assoc, mul_comm c e, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  have hcd : c * (-(d / c)) = -d := by rw [mul_neg, hcd']
  have hce : c * (-(e / c)) = -e := by rw [mul_neg, hce']
  -- (1) the linear form is killed by the substitution
  have hψL : phiSub c d e (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1
        + MvPolynomial.C e) = 0 := by
    simp only [map_add, map_mul, phiSub_C, phiSub_X0, phiSub_X1]
    rw [show Polynomial.C c * (Polynomial.C (-(d / c)) * Polynomial.X + Polynomial.C (-(e / c)))
            + Polynomial.C d * Polynomial.X + Polynomial.C e
          = Polynomial.C (c * (-(d / c))) * Polynomial.X + Polynomial.C (c * (-(e / c)))
            + Polynomial.C d * Polynomial.X + Polynomial.C e from by
        rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]]
    rw [hcd, hce, Polynomial.C_neg, Polynomial.C_neg]
    first | refl_ring1 | ring
  -- (2) hence the image of `g0p r` vanishes
  have hg : phiSub c d e (Work.MotK.TGen.g0p r) = 0 := by
    have h1 := congrArg (phiSub c d e) h
    rw [map_mul, hψL, zero_mul] at h1
    exact h1.symm
  -- (3) the coefficient of `X ^ 5`
  have hcoeff : Polynomial.coeff (phiSub c d e (Work.MotK.TGen.g0p r)) 5
      = r ^ 7 * (-(d / c)) ^ 5 - r ^ 2 := by
    have hval : phiSub c d e (Work.MotK.TGen.g0p r)
        = Polynomial.C (r ^ 7) * (Polynomial.C (-(d / c)) * Polynomial.X + Polynomial.C (-(e / c))) ^ 5
          - Polynomial.C (r ^ 3 * (3 + r ^ 5)) * (Polynomial.C (-(d / c)) * Polynomial.X + Polynomial.C (-(e / c))) ^ 2 * Polynomial.X
          + Polynomial.C (1 + 2 * r ^ 5) * (Polynomial.C (-(d / c)) * Polynomial.X + Polynomial.C (-(e / c))) * Polynomial.X ^ 3
          - Polynomial.C (r ^ 2) * Polynomial.X ^ 5 + Polynomial.C (r ^ 2) := by
      simp only [Work.MotK.TGen.g0p, map_add, map_sub, map_mul, map_neg, map_pow, phiSub_C,
        phiSub_X0, phiSub_X1]
      try ring
    rw [hval]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc]
    rw [coeff_sq_mul_X (-(d / c)) (-(e / c)), coeff_mul_X3 (-(d / c)) (-(e / c)),
      coeff_C_eq_zero (r ^ 2), coeff_linear_pow_self (-(d / c)) (-(e / c)) 5,
      Polynomial.coeff_X_pow_self]
    first | refl_ring1 | ring
  have hcoe : Polynomial.coeff (phiSub c d e (Work.MotK.TGen.g0p r)) 5 = 0 := by
    rw [hg, Polynomial.coeff_zero]
  have hmain : r ^ 7 * (-(d / c)) ^ 5 - r ^ 2 = 0 := by
    rw [← hcoeff]; exact hcoe
  have hkey : r ^ 7 * (-(d / c)) ^ 5 = r ^ 2 := sub_eq_zero.mp hmain
  have h2 : r ^ 2 * (r ^ 5 * d ^ 5 + c ^ 5) = 0 := by
    have h1 : r ^ 7 * (-(d / c)) ^ 5 * c ^ 5 = r ^ 2 * c ^ 5 := by rw [hkey]
    have hcc : (-(d / c)) ^ 5 * c ^ 5 = (-d) ^ 5 := by
      rw [← mul_pow, show -(d / c) * c = -d from by
        rw [neg_mul, mul_comm (d / c) c, hcd']]
    have h2' : r ^ 7 * (-(d / c)) ^ 5 * c ^ 5 = -(r ^ 7 * d ^ 5) := by
      rw [mul_assoc, hcc]; ring
    rw [h2'] at h1
    have h3 : r ^ 7 * d ^ 5 + r ^ 2 * c ^ 5 = 0 := by
      rw [← h1]; ring
    calc r ^ 2 * (r ^ 5 * d ^ 5 + c ^ 5)
        = r ^ 7 * d ^ 5 + r ^ 2 * c ^ 5 := by ring
      _ = 0 := h3
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have h3 : r ^ 5 * d ^ 5 + c ^ 5 = 0 := (mul_eq_zero.mp h2).resolve_left hr2
  rw [mul_pow, eq_neg_iff_add_eq_zero]
  exact h3

end Work.MotK.TGen.ZElim2AuxG
