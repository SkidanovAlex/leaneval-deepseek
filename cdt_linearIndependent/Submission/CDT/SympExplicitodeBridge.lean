import Mathlib
import Submission.CDT.SympExplicitode
import Submission.CDT.SympPullback
import Submission.CDT.SympZagier
import Submission.CDT.ZagierH

/-!
# The push-down of the order-4 operator to `x ↦ y(x)`: the bridge to the
explicit certificate (paper eq. (explicitode))

This module formalises the *bridge* of the certificate in
`Scratch/explicitode/README.md`.  See the end of this module for the
assembled statement `cleared_pullback`.

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section
open PowerSeries
namespace Submission.CDT

/-! ## 1. The unit `W = (x−1)⁻¹` -/

/-- `W = (x−1)⁻¹`, the unit whose powers clear the denominators of the
push-down. -/
def W : PowerSeries ℚ := ((X : PowerSeries ℚ) - 1)⁻¹

lemma XsubOne_ne_zero : ((X : PowerSeries ℚ) - 1) ≠ 0 := by
  intro h
  have h0 := congrArg (PowerSeries.coeff 0) h
  simp at h0

lemma XsubTwo_ne_zero : ((X : PowerSeries ℚ) - 2) ≠ 0 := by
  intro h
  have h0 : PowerSeries.coeff 0 ((X : PowerSeries ℚ) - 2) = 0 := by rw [h]; simp
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl] at h0
  simp at h0

lemma X_ne_zero : (X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h0 := congrArg (PowerSeries.coeff 1) h
  rw [PowerSeries.coeff_one_X] at h0
  simp at h0

lemma W_mul_XsubOne : W * ((X : PowerSeries ℚ) - 1) = 1 := by
  rw [W]; exact PowerSeries.inv_mul_cancel _ (by simp)

lemma XsubOne_mul_W : ((X : PowerSeries ℚ) - 1) * W = 1 := by
  rw [W]; exact PowerSeries.mul_inv_cancel _ (by simp)

lemma W_ne_zero : W ≠ 0 := by
  intro h
  have := W_mul_XsubOne
  rw [h, zero_mul] at this
  exact one_ne_zero this.symm

/-- **the basic clearing identity**: `(x−1)^j·W^k = (x−1)^{j−k}` for `k ≤ j`. -/
lemma XsubOne_pow_mul_W_pow (j k : ℕ) (h : k ≤ j) :
    ((X : PowerSeries ℚ) - 1) ^ j * W ^ k = ((X : PowerSeries ℚ) - 1) ^ (j - k) := by
  have hmul : ((X : PowerSeries ℚ) - 1) ^ k * W ^ k = 1 := by
    rw [← mul_pow, XsubOne_mul_W, one_pow]
  have hj : ((X : PowerSeries ℚ) - 1) ^ j
      = ((X : PowerSeries ℚ) - 1) ^ (j - k) * ((X : PowerSeries ℚ) - 1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [hj, mul_assoc, hmul, mul_one]

/-- the mirror image of `XsubOne_pow_mul_W_pow` -/
lemma W_pow_mul_XsubOne_pow (k j : ℕ) (h : k ≤ j) :
    W ^ k * ((X : PowerSeries ℚ) - 1) ^ j = ((X : PowerSeries ℚ) - 1) ^ (j - k) := by
  rw [mul_comm, XsubOne_pow_mul_W_pow j k h]

lemma derivative_W : (PowerSeries.derivative (R := ℚ)) W = -(W ^ 2) := by
  rw [W, PowerSeries.derivative_inv']
  simp

lemma derivative_W_pow_two : (PowerSeries.derivative (R := ℚ)) (W ^ 2) = -(2 * W ^ 3) := by
  rw [PowerSeries.derivative_pow, derivative_W]
  ring

lemma deriv_two : (PowerSeries.derivative (R := ℚ)) (2 : PowerSeries ℚ) = 0 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from rfl, PowerSeries.derivative_C]

lemma deriv_natCast (n : ℕ) : (PowerSeries.derivative (R := ℚ)) (n : PowerSeries ℚ) = 0 := by
  rw [show (n : PowerSeries ℚ) = PowerSeries.C (n : ℚ) by simp, PowerSeries.derivative_C]

lemma deriv_one : (PowerSeries.derivative (R := ℚ)) (1 : PowerSeries ℚ) = 0 := by
  rw [show (1 : PowerSeries ℚ) = PowerSeries.C (1 : ℚ) from rfl, PowerSeries.derivative_C]

/-! ## 2. `sympY` in closed form and its derivatives -/

lemma sympY_eq_X2W : sympY = (X : PowerSeries ℚ) ^ 2 * W := by
  rw [sympY, sympPhi, W]
  ring

lemma sympY_pow (k : ℕ) : sympY ^ k = (X : PowerSeries ℚ) ^ (2 * k) * W ^ k := by
  rw [sympY_eq_X2W, mul_pow, ← pow_mul]

/-- the first derivative of `y`: `y′ = X(X−2)W²`. -/
def Yp : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) sympY

/-- the second derivative of `y`: `y″ = 2W³`. -/
def Ypp : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) Yp

lemma Yp_eq : Yp = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2 := by
  rw [Yp, sympY_deriv_eq, W]

lemma Ypp_eq : Ypp = 2 * W ^ 3 := by
  have dc : (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2))
      = 2 * (X : PowerSeries ℚ) - 2 := by
    rw [Derivation.leibniz]
    simp only [derivative_X, map_sub, sub_zero, smul_eq_mul, deriv_two]
    ring
  have hcl : ((X : PowerSeries ℚ) - 1) ^ 3
        * (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2)
      = ((X : PowerSeries ℚ) - 1) ^ 3 * (2 * W ^ 3) := by
    rw [show (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2
        = ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * W ^ 2 by ring]
    rw [Derivation.leibniz, dc, derivative_W_pow_two]
    simp only [smul_eq_mul]
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3
          * (((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * (-(2 * W ^ 3))
              + W ^ 2 * (2 * (X : PowerSeries ℚ) - 2))
        = (-(2 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)))) * (W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3)
          + ((2 * (X : PowerSeries ℚ) - 2)) * (W ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 3) by ring]
    rw [show W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3 = 1 by
      rw [← mul_pow, W_mul_XsubOne, one_pow]]
    rw [W_pow_mul_XsubOne_pow 2 3 (by norm_num)]
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * (2 * W ^ 3)
        = 2 * (W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3) by ring]
    rw [show W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3 = 1 by
      rw [← mul_pow, W_mul_XsubOne, one_pow]]
    ring
  rw [Ypp, Yp, sympY_deriv_eq, show (((X : PowerSeries ℚ) - 1)⁻¹) = W from rfl]
  exact mul_left_cancel₀ (pow_ne_zero 3 XsubOne_ne_zero) hcl

lemma Yp_ne_zero : Yp ≠ 0 := by
  rw [Yp_eq]
  exact mul_ne_zero (mul_ne_zero X_ne_zero XsubTwo_ne_zero) (pow_ne_zero 2 W_ne_zero)

/-- **first key clearing**: `(x−1)²·y′ = x(x−2)`. -/
lemma XsubOne_sq_mul_Yp : ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
    = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) := by
  rw [Yp_eq]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 2
        * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2)
      = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (W ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 2) by ring]
  rw [show W ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 2 = 1 by
    rw [← mul_pow, W_mul_XsubOne, one_pow]]
  ring

/-- **second key clearing**: `(x−1)³·y′ = x(x−2)(x−1)`. -/
lemma XsubOne_cube_mul_Yp : ((X : PowerSeries ℚ) - 1) ^ 3 * Yp
    = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * ((X : PowerSeries ℚ) - 1) := by
  rw [Yp_eq]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 3
        * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2)
      = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * (W ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 3) by ring]
  rw [W_pow_mul_XsubOne_pow 2 3 (by norm_num)]
  ring

/-- **third key clearing**: `(x−1)³·y″ = 2`. -/
lemma XsubOne_cube_mul_Ypp : ((X : PowerSeries ℚ) - 1) ^ 3 * Ypp = 2 := by
  rw [Ypp_eq]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * (2 * W ^ 3) = 2 * (W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3) by ring]
  rw [show W ^ 3 * ((X : PowerSeries ℚ) - 1) ^ 3 = 1 by
    rw [← mul_pow, W_mul_XsubOne, one_pow]]
  ring

/-! ## 3. `F_i = (G_A⁽ⁱ⁾)∘y` and the chain rule -/

/-- `F_i = (G_A⁽ⁱ⁾)∘y`, the `i`-th `y`-derivative of `G_A` composed with
`y(x) = x²/(x−1)`. -/
def Ffun (i : ℕ) : PowerSeries ℚ := ((PowerSeries.derivative (R := ℚ))^[i] GA).subst sympY

lemma Ffun_zero : Ffun 0 = HAF := by
  rw [Ffun, Function.iterate_zero_apply]
  rw [show GA = sympSym HA from rfl, GA_subst_sympY]

lemma Ffun_one : Ffun 1 = GAd1.subst sympY := rfl
lemma Ffun_two : Ffun 2 = GAd2.subst sympY := rfl
lemma Ffun_three : Ffun 3 = GAd3.subst sympY := rfl
lemma Ffun_four : Ffun 4 = GAd4.subst sympY := rfl

/-- **the chain rule**: `F_{i+1}·y′ = (F_i)′`. -/
lemma Ffun_chain (i : ℕ) : Ffun (i + 1) * Yp = (PowerSeries.derivative (R := ℚ)) (Ffun i) := by
  have h := PowerSeries.derivative_subst (f := (PowerSeries.derivative (R := ℚ))^[i] GA)
      (g := sympY) sympY_hasSubst
  rw [Yp, Ffun, Ffun, Function.iterate_succ_apply']
  exact h.symm

/-! ## 4. The cleared expansions `G_i` and the inductive identity
`(x−1)^{3(i−1)}·(y′)^{2i−1}·F_i = G_i` -/

/-- `A = x(x−2)(x−1)` -/
def Ad : PowerSeries ℚ := (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * ((X : PowerSeries ℚ) - 1)

/-- `dF k = (d/dx)^k F_0` -/
def dF (k : ℕ) : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ))^[k] (Ffun 0)

lemma dF_zero : dF 0 = Ffun 0 := by simp only [dF, Function.iterate_zero_apply]

lemma dF_succ (k : ℕ) : dF (k + 1) = (PowerSeries.derivative (R := ℚ)) (dF k) := by
  simp only [dF, Ffun, Function.iterate_succ_apply', Function.iterate_zero_apply]

lemma dF_one : dF 1 = (PowerSeries.derivative (R := ℚ)) (Ffun 0) := by
  rw [show dF 1 = (PowerSeries.derivative (R := ℚ)) (dF 0) from dF_succ 0, dF_zero]

/-- the derivative of a `dF k` is `dF (k+1)` -/
lemma deriv_dF (k : ℕ) : (PowerSeries.derivative (R := ℚ)) (dF k) = dF (k + 1) :=
  (dF_succ k).symm

/-- the product rule in the form used below -/
lemma deriv_poly_mul_dF (C : PowerSeries ℚ) (k : ℕ) :
    (PowerSeries.derivative (R := ℚ)) (C * dF k)
      = ((PowerSeries.derivative (R := ℚ)) C) * dF k + C * dF (k + 1) := by
  rw [Derivation.leibniz, deriv_dF]
  simp only [smul_eq_mul]
  ring

lemma deriv_two_mul (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (2 * f) = 2 * (PowerSeries.derivative (R := ℚ)) f := by
  rw [Derivation.leibniz, deriv_two]
  simp only [smul_eq_mul]
  ring

lemma deriv_six : (PowerSeries.derivative (R := ℚ)) (6 : PowerSeries ℚ) = 0 := by
  rw [show (6 : PowerSeries ℚ) = PowerSeries.C (6 : ℚ) from rfl, PowerSeries.derivative_C]

lemma deriv_twelve : (PowerSeries.derivative (R := ℚ)) (12 : PowerSeries ℚ) = 0 := by
  rw [show (12 : PowerSeries ℚ) = PowerSeries.C (12 : ℚ) from rfl, PowerSeries.derivative_C]

lemma deriv_twentyfour : (PowerSeries.derivative (R := ℚ)) (24 : PowerSeries ℚ) = 0 := by
  rw [show (24 : PowerSeries ℚ) = PowerSeries.C (24 : ℚ) from rfl, PowerSeries.derivative_C]

lemma deriv_six_mul (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (6 * f) = 6 * (PowerSeries.derivative (R := ℚ)) f := by
  rw [Derivation.leibniz, deriv_six]
  simp only [smul_eq_mul]
  ring

lemma deriv_twelve_mul (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (12 * f) = 12 * (PowerSeries.derivative (R := ℚ)) f := by
  rw [Derivation.leibniz, deriv_twelve]
  simp only [smul_eq_mul]
  ring

lemma deriv_twentyfour_mul (f : PowerSeries ℚ) :
    (PowerSeries.derivative (R := ℚ)) (24 * f) = 24 * (PowerSeries.derivative (R := ℚ)) f := by
  rw [Derivation.leibniz, deriv_twentyfour]
  simp only [smul_eq_mul]
  ring

lemma deriv_Yp : (PowerSeries.derivative (R := ℚ)) Yp = Ypp := rfl

lemma deriv_XsubOne : (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) - 1) = 1 := by
  rw [map_sub, derivative_X, deriv_one, sub_zero]

lemma deriv_quad : (PowerSeries.derivative (R := ℚ))
    ((X : PowerSeries ℚ) ^ 2 - 2 * (X : PowerSeries ℚ) + 2) = 2 * (X : PowerSeries ℚ) - 2 := by
  rw [map_add, map_sub, deriv_two_mul,
    show (PowerSeries.derivative (R := ℚ)) (X : PowerSeries ℚ) = 1 from derivative_X, deriv_two,
    show (PowerSeries.derivative (R := ℚ)) ((X : PowerSeries ℚ) ^ 2) = 2 * (X : PowerSeries ℚ) by
      rw [PowerSeries.derivative_pow]; simp]
  ring

/-- `G_1 = F_0′` -/
def G1 : PowerSeries ℚ := dF 1
/-- `G_2 = A·F_0″ − 2F_0′` -/
def G2 : PowerSeries ℚ := Ad * dF 2 - 2 * dF 1
/-- `G_3 = A²F_0‴ − 6A·F_0″ + 6(x²−2x+2)F_0′` -/
def G3 : PowerSeries ℚ := Ad ^ 2 * dF 3 - 6 * Ad * dF 2
  + 6 * ((X : PowerSeries ℚ) ^ 2 - 2 * (X : PowerSeries ℚ) + 2) * dF 1
/-- `G_4 = A³F_0⁗ − 12A²F_0‴ + 12A(2x²−4x+5)F_0″ − 24(x⁴−4x³+9x²−10x+5)F_0′` -/
def G4 : PowerSeries ℚ := Ad ^ 3 * dF 4 - 12 * Ad ^ 2 * dF 3
  + 12 * Ad * (2 * (X : PowerSeries ℚ) ^ 2 - 4 * (X : PowerSeries ℚ) + 5) * dF 2
  - 24 * ((X : PowerSeries ℚ) ^ 4 - 4 * (X : PowerSeries ℚ) ^ 3 + 9 * (X : PowerSeries ℚ) ^ 2
      - 10 * (X : PowerSeries ℚ) + 5) * dF 1

lemma derivative_Ad : (PowerSeries.derivative (R := ℚ)) Ad
    = 3 * (X : PowerSeries ℚ) ^ 2 - 6 * (X : PowerSeries ℚ) + 2 := by
  unfold Ad
  rw [Derivation.leibniz, Derivation.leibniz]
  simp only [derivative_X, map_sub, sub_zero, smul_eq_mul, deriv_two, deriv_one]
  ring

lemma derivative_Ad_sq : (PowerSeries.derivative (R := ℚ)) (Ad ^ 2)
    = 2 * Ad * (3 * (X : PowerSeries ℚ) ^ 2 - 6 * (X : PowerSeries ℚ) + 2) := by
  rw [PowerSeries.derivative_pow, derivative_Ad]
  ring

/-- the operator recursion `G_{i+1} = A·G_i′ − 3(i−1)·x(x−2)·G_i − 2(2i−1)·G_i`,
instance `i = 1` -/
lemma G2_rec : G2 = Ad * (PowerSeries.derivative (R := ℚ)) G1 - 2 * G1 := by
  rw [G2, G1, show dF 2 = (PowerSeries.derivative (R := ℚ)) (dF 1) from dF_succ 1]

/-- the operator recursion, instance `i = 2` -/
lemma G3_rec : G3 = Ad * (PowerSeries.derivative (R := ℚ)) G2
    - 3 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * G2 - 6 * G2 := by
  rw [G2, G3, Derivation.map_sub, deriv_poly_mul_dF, derivative_Ad, deriv_two_mul, deriv_dF]
  unfold Ad
  ring

/-- the operator recursion, instance `i = 3` -/
lemma G4_rec : G4 = Ad * (PowerSeries.derivative (R := ℚ)) G3
    - 6 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * G3 - 10 * G3 := by
  rw [G3, G4, Derivation.map_add, Derivation.map_sub, deriv_poly_mul_dF, deriv_poly_mul_dF,
    deriv_poly_mul_dF, derivative_Ad_sq, deriv_six_mul, derivative_Ad, deriv_six_mul, deriv_quad]
  unfold Ad
  ring

/-- **the cleared identity, `i = 1`**: `y′·F_1 = G_1` (the chain rule). -/
lemma G_ident_one : Yp * Ffun 1 = G1 := by
  rw [G1, dF_one, mul_comm]
  exact Ffun_chain 0

/-- **step `i = 1 → 2`** of the induction. -/
lemma G_step_two (h : Yp * Ffun 1 = G1) :
    ((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 3 * Ffun 2 = G2 := by
  have hS : ((X : PowerSeries ℚ) - 1) ^ 3 * (Yp * Ffun 1) = ((X : PowerSeries ℚ) - 1) ^ 3 * G1 := by
    rw [h]
  have hL : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * (Yp * Ffun 1))
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 2 * Yp) * Ffun 1
        + (((X : PowerSeries ℚ) - 1) ^ 3 * Ypp) * Ffun 1
        + (((X : PowerSeries ℚ) - 1) ^ 3 * Yp) * (PowerSeries.derivative (R := ℚ)) (Ffun 1) := by
    rw [Derivation.leibniz, Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne, deriv_Yp]
    simp only [smul_eq_mul, mul_one]
    ring
  have hR : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G1)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 2) * G1
        + (((X : PowerSeries ℚ) - 1) ^ 3) * (PowerSeries.derivative (R := ℚ)) G1 := by
    rw [Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne]
    simp only [smul_eq_mul, mul_one]
    ring
  have hd' : (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp ^ 2) * Ffun 1
        + (((X : PowerSeries ℚ) - 1) ^ 5 * Yp * Ypp) * Ffun 1
        + (((X : PowerSeries ℚ) - 1) ^ 5 * Yp ^ 2) * (PowerSeries.derivative (R := ℚ)) (Ffun 1)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G1
        + (((X : PowerSeries ℚ) - 1) ^ 5 * Yp) * (PowerSeries.derivative (R := ℚ)) G1 := by
    have h0 : ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * (Yp * Ffun 1))
        = ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G1) := by
      rw [hS]
    rw [hL, hR] at h0
    rw [mul_add, mul_add] at h0
    convert h0 using 1 <;> ring
  have hT1 : (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp ^ 2) * Ffun 1
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G1 := by
    rw [show (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G1
        = 3 * ((X : PowerSeries ℚ) - 1) * Yp * (((X : PowerSeries ℚ) - 1) ^ 3 * G1) by ring,
      ← hS]
    ring
  have hT2 : (((X : PowerSeries ℚ) - 1) ^ 5 * Yp * Ypp) * Ffun 1
      = (2 * ((X : PowerSeries ℚ) - 1) ^ 2) * G1 := by
    rw [show (((X : PowerSeries ℚ) - 1) ^ 5 * Yp * Ypp) * Ffun 1
        = ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp
          * (((X : PowerSeries ℚ) - 1) ^ 3 * (Yp * Ffun 1)) by ring, hS]
    rw [show ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp * (((X : PowerSeries ℚ) - 1) ^ 3 * G1)
        = ((X : PowerSeries ℚ) - 1) ^ 2 * (((X : PowerSeries ℚ) - 1) ^ 3 * Ypp) * G1 by ring,
      XsubOne_cube_mul_Ypp]
    ring
  rw [hT1, hT2] at hd'
  have hkey : (((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 2) * (PowerSeries.derivative (R := ℚ)) (Ffun 1)
      = Ad * (PowerSeries.derivative (R := ℚ)) G1 - 2 * G1 := by
    have hc : ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 2) * (PowerSeries.derivative (R := ℚ)) (Ffun 1) + 2 * G1)
        = ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 3 * Yp) * (PowerSeries.derivative (R := ℚ)) G1) := by
      linear_combination (norm := ring) hd'
    have hc' := mul_left_cancel₀ (pow_ne_zero 2 XsubOne_ne_zero) hc
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * Yp = Ad from XsubOne_cube_mul_Yp] at hc'
    linear_combination (norm := ring) hc'
  rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 3 * Ffun 2
      = ((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 2 * (PowerSeries.derivative (R := ℚ)) (Ffun 1) by
    rw [show Ffun 2 = Ffun (1 + 1) from rfl, ← Ffun_chain 1]; ring]
  rw [hkey, ← G2_rec]

/-- **step `i = 2 → 3`** of the induction. -/
lemma G_step_three (h : ((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 3 * Ffun 2 = G2) :
    ((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 5 * Ffun 3 = G3 := by
  have hS : ((X : PowerSeries ℚ) - 1) ^ 6 * (Yp ^ 3 * Ffun 2)
      = ((X : PowerSeries ℚ) - 1) ^ 3 * G2 := by
    rw [← h]; ring
  have hL : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 6 * (Yp ^ 3 * Ffun 2))
      = (6 * ((X : PowerSeries ℚ) - 1) ^ 5 * Yp ^ 3) * Ffun 2
        + (((X : PowerSeries ℚ) - 1) ^ 6 * (3 * Yp ^ 2 * Ypp)) * Ffun 2
        + (((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 3) * (PowerSeries.derivative (R := ℚ)) (Ffun 2) := by
    simp only [Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne, deriv_Yp,
      smul_eq_mul, mul_one]
    ring
  have hR : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G2)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 2) * G2
        + (((X : PowerSeries ℚ) - 1) ^ 3) * (PowerSeries.derivative (R := ℚ)) G2 := by
    rw [Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne]
    simp only [smul_eq_mul, mul_one]
    ring
  have hd' : (6 * ((X : PowerSeries ℚ) - 1) ^ 7 * Yp ^ 4) * Ffun 2
        + (((X : PowerSeries ℚ) - 1) ^ 8 * (3 * Yp ^ 3 * Ypp)) * Ffun 2
        + (((X : PowerSeries ℚ) - 1) ^ 8 * Yp ^ 4) * (PowerSeries.derivative (R := ℚ)) (Ffun 2)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G2
        + (((X : PowerSeries ℚ) - 1) ^ 5 * Yp) * (PowerSeries.derivative (R := ℚ)) G2 := by
    have h0 : ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 6 * (Yp ^ 3 * Ffun 2))
        = ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G2) := by
      rw [hS]
    rw [hL, hR] at h0
    rw [mul_add, mul_add] at h0
    convert h0 using 1 <;> ring
  have hT1 : (6 * ((X : PowerSeries ℚ) - 1) ^ 7 * Yp ^ 4) * Ffun 2
      = (6 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G2 := by
    rw [show (6 * ((X : PowerSeries ℚ) - 1) ^ 7 * Yp ^ 4) * Ffun 2
        = 6 * ((X : PowerSeries ℚ) - 1) * Yp * (((X : PowerSeries ℚ) - 1) ^ 6 * (Yp ^ 3 * Ffun 2)) by ring,
      hS]
    ring
  have hT2 : (((X : PowerSeries ℚ) - 1) ^ 8 * (3 * Yp ^ 3 * Ypp)) * Ffun 2
      = (6 * ((X : PowerSeries ℚ) - 1) ^ 2) * G2 := by
    rw [show (((X : PowerSeries ℚ) - 1) ^ 8 * (3 * Yp ^ 3 * Ypp)) * Ffun 2
        = 3 * ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp
          * (((X : PowerSeries ℚ) - 1) ^ 6 * (Yp ^ 3 * Ffun 2)) by ring, hS]
    rw [show 3 * ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp * (((X : PowerSeries ℚ) - 1) ^ 3 * G2)
        = 3 * ((X : PowerSeries ℚ) - 1) ^ 2 * (((X : PowerSeries ℚ) - 1) ^ 3 * Ypp) * G2 by ring,
      XsubOne_cube_mul_Ypp]
    ring
  rw [hT1, hT2] at hd'
  have hkey : (((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 4) * (PowerSeries.derivative (R := ℚ)) (Ffun 2)
      = Ad * (PowerSeries.derivative (R := ℚ)) G2
        - 3 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * G2 - 6 * G2 := by
    have hc : ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 4) * (PowerSeries.derivative (R := ℚ)) (Ffun 2)
              + 3 * (((X : PowerSeries ℚ) - 1) ^ 2 * Yp) * G2 + 6 * G2)
        = ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 3 * Yp) * (PowerSeries.derivative (R := ℚ)) G2) := by
      linear_combination (norm := ring) hd'
    have hc' := mul_left_cancel₀ (pow_ne_zero 2 XsubOne_ne_zero) hc
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * Yp = Ad from XsubOne_cube_mul_Yp,
      show ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
        = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) from XsubOne_sq_mul_Yp] at hc'
    linear_combination (norm := ring) hc'
  rw [show ((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 5 * Ffun 3
      = ((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 4 * (PowerSeries.derivative (R := ℚ)) (Ffun 2) by
    rw [show Ffun 3 = Ffun (2 + 1) from rfl, ← Ffun_chain 2]; ring]
  rw [hkey, ← G3_rec]

/-- **step `i = 3 → 4`** of the induction. -/
lemma G_step_four (h : ((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 5 * Ffun 3 = G3) :
    ((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 7 * Ffun 4 = G4 := by
  have hS : ((X : PowerSeries ℚ) - 1) ^ 9 * (Yp ^ 5 * Ffun 3)
      = ((X : PowerSeries ℚ) - 1) ^ 3 * G3 := by
    rw [← h]; ring
  have hL : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 9 * (Yp ^ 5 * Ffun 3))
      = (9 * ((X : PowerSeries ℚ) - 1) ^ 8 * Yp ^ 5) * Ffun 3
        + (((X : PowerSeries ℚ) - 1) ^ 9 * (5 * Yp ^ 4 * Ypp)) * Ffun 3
        + (((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 5) * (PowerSeries.derivative (R := ℚ)) (Ffun 3) := by
    simp only [Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne, deriv_Yp,
      smul_eq_mul, mul_one]
    ring
  have hR : (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G3)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 2) * G3
        + (((X : PowerSeries ℚ) - 1) ^ 3) * (PowerSeries.derivative (R := ℚ)) G3 := by
    rw [Derivation.leibniz, PowerSeries.derivative_pow, deriv_XsubOne]
    simp only [smul_eq_mul, mul_one]
    ring
  have hd' : (9 * ((X : PowerSeries ℚ) - 1) ^ 10 * Yp ^ 6) * Ffun 3
        + (((X : PowerSeries ℚ) - 1) ^ 11 * (5 * Yp ^ 5 * Ypp)) * Ffun 3
        + (((X : PowerSeries ℚ) - 1) ^ 11 * Yp ^ 6) * (PowerSeries.derivative (R := ℚ)) (Ffun 3)
      = (3 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G3
        + (((X : PowerSeries ℚ) - 1) ^ 5 * Yp) * (PowerSeries.derivative (R := ℚ)) G3 := by
    have h0 : ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 9 * (Yp ^ 5 * Ffun 3))
        = ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
          * (PowerSeries.derivative (R := ℚ)) (((X : PowerSeries ℚ) - 1) ^ 3 * G3) := by
      rw [hS]
    rw [hL, hR] at h0
    rw [mul_add, mul_add] at h0
    convert h0 using 1 <;> ring
  have hT1 : (9 * ((X : PowerSeries ℚ) - 1) ^ 10 * Yp ^ 6) * Ffun 3
      = (9 * ((X : PowerSeries ℚ) - 1) ^ 4 * Yp) * G3 := by
    rw [show (9 * ((X : PowerSeries ℚ) - 1) ^ 10 * Yp ^ 6) * Ffun 3
        = 9 * ((X : PowerSeries ℚ) - 1) * Yp
          * (((X : PowerSeries ℚ) - 1) ^ 9 * (Yp ^ 5 * Ffun 3)) by ring, hS]
    ring
  have hT2 : (((X : PowerSeries ℚ) - 1) ^ 11 * (5 * Yp ^ 5 * Ypp)) * Ffun 3
      = (10 * ((X : PowerSeries ℚ) - 1) ^ 2) * G3 := by
    rw [show (((X : PowerSeries ℚ) - 1) ^ 11 * (5 * Yp ^ 5 * Ypp)) * Ffun 3
        = 5 * ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp
          * (((X : PowerSeries ℚ) - 1) ^ 9 * (Yp ^ 5 * Ffun 3)) by ring, hS]
    rw [show 5 * ((X : PowerSeries ℚ) - 1) ^ 2 * Ypp * (((X : PowerSeries ℚ) - 1) ^ 3 * G3)
        = 5 * ((X : PowerSeries ℚ) - 1) ^ 2 * (((X : PowerSeries ℚ) - 1) ^ 3 * Ypp) * G3 by ring,
      XsubOne_cube_mul_Ypp]
    ring
  rw [hT1, hT2] at hd'
  have hkey : (((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 6) * (PowerSeries.derivative (R := ℚ)) (Ffun 3)
      = Ad * (PowerSeries.derivative (R := ℚ)) G3
        - 6 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2)) * G3 - 10 * G3 := by
    have hc : ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 6) * (PowerSeries.derivative (R := ℚ)) (Ffun 3)
              + 6 * (((X : PowerSeries ℚ) - 1) ^ 2 * Yp) * G3 + 10 * G3)
        = ((X : PowerSeries ℚ) - 1) ^ 2
          * ((((X : PowerSeries ℚ) - 1) ^ 3 * Yp) * (PowerSeries.derivative (R := ℚ)) G3) := by
      linear_combination (norm := ring) hd'
    have hc' := mul_left_cancel₀ (pow_ne_zero 2 XsubOne_ne_zero) hc
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * Yp = Ad from XsubOne_cube_mul_Yp,
      show ((X : PowerSeries ℚ) - 1) ^ 2 * Yp
        = (X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) from XsubOne_sq_mul_Yp] at hc'
    linear_combination (norm := ring) hc'
  rw [show ((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 7 * Ffun 4
      = ((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 6 * (PowerSeries.derivative (R := ℚ)) (Ffun 3) by
    rw [show Ffun 4 = Ffun (3 + 1) from rfl, ← Ffun_chain 3]; ring]
  rw [hkey, ← G4_rec]


lemma C_int (z : ℤ) : PowerSeries.C (z : ℚ) = (z : PowerSeries ℚ) :=
  map_intCast PowerSeries.C z

/-! ## 5. Clearing the multipliers `c_i ∘ y`

For `i ≥ 1` the product `(x−1)^{6+i}·(cᵢ∘y)` is a *polynomial* `Pᵢ` (and
`(x−1)^5·(c₀∘y) = P₀`) — the facts that turn `(x−1)^19·y′⁷·(cᵢ∘y)·Fᵢ` into a
polynomial coefficient times `Gᵢ`.  `qᵢ` is the explicit polynomial form of
the paper's multiplier `cᵢ` (matching the `mk`-defined `cᵢY` of
`SympExplicitode`).  The coefficients are written as integer casts so that
`ring` can evaluate them (via `C_int`). -/

/-- the paper's multiplier `c0` as an explicit polynomial -/
def q0 : Polynomial ℚ :=
  Polynomial.C ((-54:ℤ):ℚ)
  + Polynomial.C ((-2268:ℤ):ℚ) * Polynomial.X ^ 1
  + Polynomial.C ((12816:ℤ):ℚ) * Polynomial.X ^ 2
  + Polynomial.C ((-6480:ℤ):ℚ) * Polynomial.X ^ 3
/-- the paper's multiplier `c1` as an explicit polynomial -/
def q1 : Polynomial ℚ :=
  Polynomial.C ((-4:ℤ):ℚ)
  + Polynomial.C ((-5522:ℤ):ℚ) * Polynomial.X ^ 1
  + Polynomial.C ((283264:ℤ):ℚ) * Polynomial.X ^ 2
  + Polynomial.C ((-560656:ℤ):ℚ) * Polynomial.X ^ 3
  + Polynomial.C ((352824:ℤ):ℚ) * Polynomial.X ^ 4
  + Polynomial.C ((-191232:ℤ):ℚ) * Polynomial.X ^ 5
  + Polynomial.C ((41472:ℤ):ℚ) * Polynomial.X ^ 6
/-- the paper's multiplier `c2` as an explicit polynomial -/
def q2 : Polynomial ℚ :=
  Polynomial.C ((-68:ℤ):ℚ) * Polynomial.X ^ 1
  + Polynomial.C ((-12706:ℤ):ℚ) * Polynomial.X ^ 2
  + Polynomial.C ((1380710:ℤ):ℚ) * Polynomial.X ^ 3
  + Polynomial.C ((-2131226:ℤ):ℚ) * Polynomial.X ^ 4
  + Polynomial.C ((1735752:ℤ):ℚ) * Polynomial.X ^ 5
  + Polynomial.C ((-876672:ℤ):ℚ) * Polynomial.X ^ 6
  + Polynomial.C ((145152:ℤ):ℚ) * Polynomial.X ^ 7
/-- the paper's multiplier `c3` as an explicit polynomial -/
def q3 : Polynomial ℚ :=
  Polynomial.C ((-80:ℤ):ℚ) * Polynomial.X ^ 2
  + Polynomial.C ((-1612:ℤ):ℚ) * Polynomial.X ^ 3
  + Polynomial.C ((945968:ℤ):ℚ) * Polynomial.X ^ 4
  + Polynomial.C ((-1411958:ℤ):ℚ) * Polynomial.X ^ 5
  + Polynomial.C ((1436676:ℤ):ℚ) * Polynomial.X ^ 6
  + Polynomial.C ((-617472:ℤ):ℚ) * Polynomial.X ^ 7
  + Polynomial.C ((82944:ℤ):ℚ) * Polynomial.X ^ 8
/-- the paper's multiplier `c4` as an explicit polynomial -/
def q4 : Polynomial ℚ :=
  Polynomial.C ((-16:ℤ):ℚ) * Polynomial.X ^ 3
  + Polynomial.C ((744:ℤ):ℚ) * Polynomial.X ^ 4
  + Polynomial.C ((133615:ℤ):ℚ) * Polynomial.X ^ 5
  + Polynomial.C ((-205186:ℤ):ℚ) * Polynomial.X ^ 6
  + Polynomial.C ((243382:ℤ):ℚ) * Polynomial.X ^ 7
  + Polynomial.C ((-91584:ℤ):ℚ) * Polynomial.X ^ 8
  + Polynomial.C ((10368:ℤ):ℚ) * Polynomial.X ^ 9

lemma c0Y_eq : c0Y = (q0 : PowerSeries ℚ) := by
  ext n
  rw [c0Y, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simp only [q0, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;> simp
lemma c1Y_eq : c1Y = (q1 : PowerSeries ℚ) := by
  ext n
  rw [c1Y, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simp only [q1, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;> simp
lemma c2Y_eq : c2Y = (q2 : PowerSeries ℚ) := by
  ext n
  rw [c2Y, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simp only [q2, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;> simp
lemma c3Y_eq : c3Y = (q3 : PowerSeries ℚ) := by
  ext n
  rw [c3Y, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simp only [q3, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;> simp
lemma c4Y_eq : c4Y = (q4 : PowerSeries ℚ) := by
  ext n
  rw [c4Y, PowerSeries.coeff_mk, Polynomial.coeff_coe]
  simp only [q4, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;> simp

lemma aeval_q0 : Polynomial.aeval sympY q0 =
    PowerSeries.C ((-54:ℤ):ℚ) + PowerSeries.C ((-2268:ℤ):ℚ) * sympY + PowerSeries.C ((12816:ℤ):ℚ) * sympY ^ 2 + PowerSeries.C ((-6480:ℤ):ℚ) * sympY ^ 3 := by
  simp only [q0, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow,
    PowerSeries.algebraMap_eq]
  try ring
lemma aeval_q1 : Polynomial.aeval sympY q1 =
    PowerSeries.C ((-4:ℤ):ℚ) + PowerSeries.C ((-5522:ℤ):ℚ) * sympY + PowerSeries.C ((283264:ℤ):ℚ) * sympY ^ 2 + PowerSeries.C ((-560656:ℤ):ℚ) * sympY ^ 3 + PowerSeries.C ((352824:ℤ):ℚ) * sympY ^ 4 + PowerSeries.C ((-191232:ℤ):ℚ) * sympY ^ 5 + PowerSeries.C ((41472:ℤ):ℚ) * sympY ^ 6 := by
  simp only [q1, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow,
    PowerSeries.algebraMap_eq]
  try ring
lemma aeval_q2 : Polynomial.aeval sympY q2 =
    PowerSeries.C ((-68:ℤ):ℚ) * sympY + PowerSeries.C ((-12706:ℤ):ℚ) * sympY ^ 2 + PowerSeries.C ((1380710:ℤ):ℚ) * sympY ^ 3 + PowerSeries.C ((-2131226:ℤ):ℚ) * sympY ^ 4 + PowerSeries.C ((1735752:ℤ):ℚ) * sympY ^ 5 + PowerSeries.C ((-876672:ℤ):ℚ) * sympY ^ 6 + PowerSeries.C ((145152:ℤ):ℚ) * sympY ^ 7 := by
  simp only [q2, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow,
    PowerSeries.algebraMap_eq]
  try ring
lemma aeval_q3 : Polynomial.aeval sympY q3 =
    PowerSeries.C ((-80:ℤ):ℚ) * sympY ^ 2 + PowerSeries.C ((-1612:ℤ):ℚ) * sympY ^ 3 + PowerSeries.C ((945968:ℤ):ℚ) * sympY ^ 4 + PowerSeries.C ((-1411958:ℤ):ℚ) * sympY ^ 5 + PowerSeries.C ((1436676:ℤ):ℚ) * sympY ^ 6 + PowerSeries.C ((-617472:ℤ):ℚ) * sympY ^ 7 + PowerSeries.C ((82944:ℤ):ℚ) * sympY ^ 8 := by
  simp only [q3, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow,
    PowerSeries.algebraMap_eq]
  try ring
lemma aeval_q4 : Polynomial.aeval sympY q4 =
    PowerSeries.C ((-16:ℤ):ℚ) * sympY ^ 3 + PowerSeries.C ((744:ℤ):ℚ) * sympY ^ 4 + PowerSeries.C ((133615:ℤ):ℚ) * sympY ^ 5 + PowerSeries.C ((-205186:ℤ):ℚ) * sympY ^ 6 + PowerSeries.C ((243382:ℤ):ℚ) * sympY ^ 7 + PowerSeries.C ((-91584:ℤ):ℚ) * sympY ^ 8 + PowerSeries.C ((10368:ℤ):ℚ) * sympY ^ 9 := by
  simp only [q4, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_pow,
    PowerSeries.algebraMap_eq]
  try ring

/-- `P0 = (x−1)^5·(c0∘y)`, a polynomial -/
def P0 : PowerSeries ℚ :=
  PowerSeries.C ((-54:ℤ):ℚ) * ((X : PowerSeries ℚ) - 1) ^ 5
  + PowerSeries.C ((-2268:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 4
  + PowerSeries.C ((12816:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 3
  + PowerSeries.C ((-6480:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 2
/-- `P1 = (x−1)^7·(c1∘y)`, a polynomial -/
def P1 : PowerSeries ℚ :=
  PowerSeries.C ((-4:ℤ):ℚ) * ((X : PowerSeries ℚ) - 1) ^ 7
  + PowerSeries.C ((-5522:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 6
  + PowerSeries.C ((283264:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 5
  + PowerSeries.C ((-560656:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 4
  + PowerSeries.C ((352824:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 8 * ((X : PowerSeries ℚ) - 1) ^ 3
  + PowerSeries.C ((-191232:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 10 * ((X : PowerSeries ℚ) - 1) ^ 2
  + PowerSeries.C ((41472:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 12 * ((X : PowerSeries ℚ) - 1) ^ 1
/-- `P2 = (x−1)^8·(c2∘y)`, a polynomial -/
def P2 : PowerSeries ℚ :=
  PowerSeries.C ((-68:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 7
  + PowerSeries.C ((-12706:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 6
  + PowerSeries.C ((1380710:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 5
  + PowerSeries.C ((-2131226:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 8 * ((X : PowerSeries ℚ) - 1) ^ 4
  + PowerSeries.C ((1735752:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 10 * ((X : PowerSeries ℚ) - 1) ^ 3
  + PowerSeries.C ((-876672:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 12 * ((X : PowerSeries ℚ) - 1) ^ 2
  + PowerSeries.C ((145152:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 14 * ((X : PowerSeries ℚ) - 1) ^ 1
/-- `P3 = (x−1)^9·(c3∘y)`, a polynomial -/
def P3 : PowerSeries ℚ :=
  PowerSeries.C ((-80:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 7
  + PowerSeries.C ((-1612:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 6
  + PowerSeries.C ((945968:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 8 * ((X : PowerSeries ℚ) - 1) ^ 5
  + PowerSeries.C ((-1411958:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 10 * ((X : PowerSeries ℚ) - 1) ^ 4
  + PowerSeries.C ((1436676:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 12 * ((X : PowerSeries ℚ) - 1) ^ 3
  + PowerSeries.C ((-617472:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 14 * ((X : PowerSeries ℚ) - 1) ^ 2
  + PowerSeries.C ((82944:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 16 * ((X : PowerSeries ℚ) - 1) ^ 1
/-- `P4 = (x−1)^10·(c4∘y)`, a polynomial -/
def P4 : PowerSeries ℚ :=
  PowerSeries.C ((-16:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 7
  + PowerSeries.C ((744:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 8 * ((X : PowerSeries ℚ) - 1) ^ 6
  + PowerSeries.C ((133615:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 10 * ((X : PowerSeries ℚ) - 1) ^ 5
  + PowerSeries.C ((-205186:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 12 * ((X : PowerSeries ℚ) - 1) ^ 4
  + PowerSeries.C ((243382:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 14 * ((X : PowerSeries ℚ) - 1) ^ 3
  + PowerSeries.C ((-91584:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 16 * ((X : PowerSeries ℚ) - 1) ^ 2
  + PowerSeries.C ((10368:ℤ):ℚ) * (X : PowerSeries ℚ) ^ 18 * ((X : PowerSeries ℚ) - 1) ^ 1

lemma clear_c0 : ((X : PowerSeries ℚ) - 1) ^ 5 * (c0Y.subst sympY) = P0 := by
  rw [c0Y_eq, PowerSeries.subst_coe sympY_hasSubst, aeval_q0, sympY_eq_X2W]
  unfold P0
  rw [← XsubOne_pow_mul_W_pow 5 1 (by norm_num : 1 ≤ 5),
    ← XsubOne_pow_mul_W_pow 5 2 (by norm_num : 2 ≤ 5),
    ← XsubOne_pow_mul_W_pow 5 3 (by norm_num : 3 ≤ 5)]
  ring
lemma clear_c1 : ((X : PowerSeries ℚ) - 1) ^ 7 * (c1Y.subst sympY) = P1 := by
  rw [c1Y_eq, PowerSeries.subst_coe sympY_hasSubst, aeval_q1, sympY_eq_X2W]
  unfold P1
  rw [← XsubOne_pow_mul_W_pow 7 1 (by norm_num : 1 ≤ 7),
    ← XsubOne_pow_mul_W_pow 7 2 (by norm_num : 2 ≤ 7),
    ← XsubOne_pow_mul_W_pow 7 3 (by norm_num : 3 ≤ 7),
    ← XsubOne_pow_mul_W_pow 7 4 (by norm_num : 4 ≤ 7),
    ← XsubOne_pow_mul_W_pow 7 5 (by norm_num : 5 ≤ 7),
    ← XsubOne_pow_mul_W_pow 7 6 (by norm_num : 6 ≤ 7)]
  ring
lemma clear_c2 : ((X : PowerSeries ℚ) - 1) ^ 8 * (c2Y.subst sympY) = P2 := by
  rw [c2Y_eq, PowerSeries.subst_coe sympY_hasSubst, aeval_q2, sympY_eq_X2W]
  unfold P2
  rw [← XsubOne_pow_mul_W_pow 8 1 (by norm_num : 1 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 2 (by norm_num : 2 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 3 (by norm_num : 3 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 4 (by norm_num : 4 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 5 (by norm_num : 5 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 6 (by norm_num : 6 ≤ 8),
    ← XsubOne_pow_mul_W_pow 8 7 (by norm_num : 7 ≤ 8)]
  ring
lemma clear_c3 : ((X : PowerSeries ℚ) - 1) ^ 9 * (c3Y.subst sympY) = P3 := by
  rw [c3Y_eq, PowerSeries.subst_coe sympY_hasSubst, aeval_q3, sympY_eq_X2W]
  unfold P3
  rw [← XsubOne_pow_mul_W_pow 9 2 (by norm_num : 2 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 3 (by norm_num : 3 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 4 (by norm_num : 4 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 5 (by norm_num : 5 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 6 (by norm_num : 6 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 7 (by norm_num : 7 ≤ 9),
    ← XsubOne_pow_mul_W_pow 9 8 (by norm_num : 8 ≤ 9)]
  ring
lemma clear_c4 : ((X : PowerSeries ℚ) - 1) ^ 10 * (c4Y.subst sympY) = P4 := by
  rw [c4Y_eq, PowerSeries.subst_coe sympY_hasSubst, aeval_q4, sympY_eq_X2W]
  unfold P4
  rw [← XsubOne_pow_mul_W_pow 10 3 (by norm_num : 3 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 4 (by norm_num : 4 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 5 (by norm_num : 5 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 6 (by norm_num : 6 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 7 (by norm_num : 7 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 8 (by norm_num : 8 ≤ 10),
    ← XsubOne_pow_mul_W_pow 10 9 (by norm_num : 9 ≤ 10)]
  ring

/-! ## 6. The bridge: `(x−1)^19·(y′)⁷·(GA_odeLHS ∘ y) = Σ_j Mp_j·F₀⁽ʲ⁾` -/

/-- the assembled coefficients `Mp_j` of the cleared pull-back,
`Mp_j = δ_{j0}·x⁷(x−2)⁷·P₀ + Σ_{i=1}^4 â^{(i)}_j·x^{8−2i}(x−2)^{8−2i}·Pᵢ`,
where the `â^{(i)}_j` are the coefficients of `G_i` in the `dF j`. -/
def Mp0 : PowerSeries ℚ := (X : PowerSeries ℚ) ^ 7 * ((X : PowerSeries ℚ) - 2) ^ 7 * P0
def Mp1 : PowerSeries ℚ := (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 2) ^ 6 * P1
  - 2 * ((X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * P2)
  + 6 * (((X : PowerSeries ℚ) ^ 2 - 2 * (X : PowerSeries ℚ) + 2) * ((X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * P3))
  - 24 * (((X : PowerSeries ℚ) ^ 4 - 4 * (X : PowerSeries ℚ) ^ 3 + 9 * (X : PowerSeries ℚ) ^ 2 - 10 * (X : PowerSeries ℚ) + 5) * P4)
def Mp2 : PowerSeries ℚ := Ad * ((X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * P2)
  - 6 * (Ad * ((X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * P3))
  + 12 * (Ad * (2 * (X : PowerSeries ℚ) ^ 2 - 4 * (X : PowerSeries ℚ) + 5) * P4)
def Mp3 : PowerSeries ℚ := Ad ^ 2 * ((X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * P3) - 12 * (Ad ^ 2 * P4)
def Mp4 : PowerSeries ℚ := Ad ^ 3 * P4

lemma GA_subst_eq_Ffun0 : GA.subst sympY = Ffun 0 := by
  rw [Ffun_zero, show GA.subst sympY = (sympSym HA).subst sympY from rfl, GA_subst_sympY]

/-- the pull-back of the operator is the sum of the five multiplied pieces -/
lemma subst_GA_odeLHS :
    GA_odeLHS.subst sympY = (c0Y.subst sympY) * Ffun 0 + (c1Y.subst sympY) * Ffun 1
      + (c2Y.subst sympY) * Ffun 2 + (c3Y.subst sympY) * Ffun 3
      + (c4Y.subst sympY) * Ffun 4 := by
  unfold GA_odeLHS
  rw [PowerSeries.subst_add sympY_hasSubst, PowerSeries.subst_add sympY_hasSubst,
    PowerSeries.subst_add sympY_hasSubst, PowerSeries.subst_add sympY_hasSubst,
    PowerSeries.subst_mul sympY_hasSubst, PowerSeries.subst_mul sympY_hasSubst,
    PowerSeries.subst_mul sympY_hasSubst, PowerSeries.subst_mul sympY_hasSubst,
    PowerSeries.subst_mul sympY_hasSubst]
  rw [show GA.subst sympY = Ffun 0 from GA_subst_eq_Ffun0,
    show GAd1.subst sympY = Ffun 1 from Ffun_one.symm,
    show GAd2.subst sympY = Ffun 2 from Ffun_two.symm,
    show GAd3.subst sympY = Ffun 3 from Ffun_three.symm,
    show GAd4.subst sympY = Ffun 4 from Ffun_four.symm]

lemma XsubOne_19_mul_Yp_seven : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7
    = (X : PowerSeries ℚ) ^ 7 * ((X : PowerSeries ℚ) - 2) ^ 7 * ((X : PowerSeries ℚ) - 1) ^ 5 := by
  rw [Yp_eq]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * ((X : PowerSeries ℚ) * ((X : PowerSeries ℚ) - 2) * W ^ 2) ^ 7
      = (X : PowerSeries ℚ) ^ 7 * ((X : PowerSeries ℚ) - 2) ^ 7 * (((X : PowerSeries ℚ) - 1) ^ 19 * W ^ 14) by ring]
  rw [XsubOne_pow_mul_W_pow 19 14 (by norm_num)]

private lemma Yp_pow_clear (k j : ℕ) (h : 2 * k ≤ j) :
    ((X : PowerSeries ℚ) - 1) ^ j * Yp ^ k = (X : PowerSeries ℚ) ^ k * ((X : PowerSeries ℚ) - 2) ^ k * ((X : PowerSeries ℚ) - 1) ^ (j - 2 * k) := by
  rw [show Yp ^ k = (X : PowerSeries ℚ) ^ k * ((X : PowerSeries ℚ) - 2) ^ k * W ^ (2 * k) by
    rw [Yp_eq, mul_pow, mul_pow, ← pow_mul]]
  rw [show ((X : PowerSeries ℚ) - 1) ^ j * ((X : PowerSeries ℚ) ^ k * ((X : PowerSeries ℚ) - 2) ^ k * W ^ (2 * k))
      = (X : PowerSeries ℚ) ^ k * ((X : PowerSeries ℚ) - 2) ^ k * (((X : PowerSeries ℚ) - 1) ^ j * W ^ (2 * k)) by ring]
  rw [XsubOne_pow_mul_W_pow j (2 * k) h]

lemma G_ident_two : ((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 3 * Ffun 2 = G2 := G_step_two G_ident_one
lemma G_ident_three : ((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 5 * Ffun 3 = G3 := G_step_three G_ident_two
lemma G_ident_four : ((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 7 * Ffun 4 = G4 := G_step_four G_ident_three

lemma term0 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c0Y.subst sympY) * Ffun 0) = Mp0 * Ffun 0 := by
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c0Y.subst sympY) * Ffun 0)
      = (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * (c0Y.subst sympY)) * Ffun 0 by ring]
  rw [XsubOne_19_mul_Yp_seven]
  rw [show (X : PowerSeries ℚ) ^ 7 * ((X : PowerSeries ℚ) - 2) ^ 7 * ((X : PowerSeries ℚ) - 1) ^ 5 * (c0Y.subst sympY)
      = (X : PowerSeries ℚ) ^ 7 * ((X : PowerSeries ℚ) - 2) ^ 7 * (((X : PowerSeries ℚ) - 1) ^ 5 * (c0Y.subst sympY)) by ring, clear_c0]
  rw [Mp0]

lemma term1 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c1Y.subst sympY) * Ffun 1)
    = ((X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 2) ^ 6 * P1) * G1 := by
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c1Y.subst sympY) * Ffun 1)
      = ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 6 * ((c1Y.subst sympY) * (Yp * Ffun 1)) by ring]
  rw [G_ident_one]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 6
      = (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 2) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 7 from Yp_pow_clear 6 19 (by norm_num)]
  rw [show (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 2) ^ 6 * ((X : PowerSeries ℚ) - 1) ^ 7 * ((c1Y.subst sympY) * G1)
      = (X : PowerSeries ℚ) ^ 6 * ((X : PowerSeries ℚ) - 2) ^ 6 * ((((X : PowerSeries ℚ) - 1) ^ 7 * (c1Y.subst sympY)) * G1) by ring]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 7 * (c1Y.subst sympY) = P1 from clear_c1]
  ring

lemma term2 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c2Y.subst sympY) * Ffun 2)
    = ((X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * P2) * G2 := by
  have hcore : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 2 = ((X : PowerSeries ℚ) - 1) ^ 16 * Yp ^ 4 * G2 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 XsubOne_ne_zero)
    rw [show ((X : PowerSeries ℚ) - 1) ^ 3 * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 2)
        = ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 4 * ((((X : PowerSeries ℚ) - 1) ^ 3 * Yp ^ 3) * Ffun 2) by ring, G_ident_two]
    ring
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c2Y.subst sympY) * Ffun 2)
      = (c2Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 2) by ring, hcore]
  rw [show (c2Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 16 * Yp ^ 4 * G2)
      = (((X : PowerSeries ℚ) - 1) ^ 16 * Yp ^ 4 * (c2Y.subst sympY)) * G2 by ring]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 16 * Yp ^ 4
      = (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 8 from Yp_pow_clear 4 16 (by norm_num)]
  rw [show (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * ((X : PowerSeries ℚ) - 1) ^ 8 * (c2Y.subst sympY)
      = (X : PowerSeries ℚ) ^ 4 * ((X : PowerSeries ℚ) - 2) ^ 4 * (((X : PowerSeries ℚ) - 1) ^ 8 * (c2Y.subst sympY)) by ring,
    show ((X : PowerSeries ℚ) - 1) ^ 8 * (c2Y.subst sympY) = P2 from clear_c2]

lemma term3 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c3Y.subst sympY) * Ffun 3)
    = ((X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * P3) * G3 := by
  have hcore : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 3 = ((X : PowerSeries ℚ) - 1) ^ 13 * Yp ^ 2 * G3 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 XsubOne_ne_zero)
    rw [show ((X : PowerSeries ℚ) - 1) ^ 6 * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 3)
        = ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 2 * ((((X : PowerSeries ℚ) - 1) ^ 6 * Yp ^ 5) * Ffun 3) by ring, G_ident_three]
    ring
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c3Y.subst sympY) * Ffun 3)
      = (c3Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 3) by ring, hcore]
  rw [show (c3Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 13 * Yp ^ 2 * G3)
      = (((X : PowerSeries ℚ) - 1) ^ 13 * Yp ^ 2 * (c3Y.subst sympY)) * G3 by ring]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 13 * Yp ^ 2
      = (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 9 from Yp_pow_clear 2 13 (by norm_num)]
  rw [show (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * ((X : PowerSeries ℚ) - 1) ^ 9 * (c3Y.subst sympY)
      = (X : PowerSeries ℚ) ^ 2 * ((X : PowerSeries ℚ) - 2) ^ 2 * (((X : PowerSeries ℚ) - 1) ^ 9 * (c3Y.subst sympY)) by ring,
    show ((X : PowerSeries ℚ) - 1) ^ 9 * (c3Y.subst sympY) = P3 from clear_c3]

lemma term4 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c4Y.subst sympY) * Ffun 4) = P4 * G4 := by
  have hcore : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 4 = ((X : PowerSeries ℚ) - 1) ^ 10 * G4 := by
    apply mul_left_cancel₀ (pow_ne_zero 9 XsubOne_ne_zero)
    rw [show ((X : PowerSeries ℚ) - 1) ^ 9 * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 4)
        = ((X : PowerSeries ℚ) - 1) ^ 19 * ((((X : PowerSeries ℚ) - 1) ^ 9 * Yp ^ 7) * Ffun 4) by ring, G_ident_four]
    ring
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c4Y.subst sympY) * Ffun 4)
      = (c4Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * Ffun 4) by ring, hcore]
  rw [show (c4Y.subst sympY) * (((X : PowerSeries ℚ) - 1) ^ 10 * G4)
      = (((X : PowerSeries ℚ) - 1) ^ 10 * (c4Y.subst sympY)) * G4 by ring]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 10 * (c4Y.subst sympY) = P4 from clear_c4]

/-- **THE BRIDGE**: the pull-back of the paper's order-4 operator, cleared by
`(x−1)^19·(y′)⁷`, is the explicit polynomial-coefficient operator
`Σ_j Mp_j·(d/dx)^j` applied to `F₀ = (Sym⁺H_A)∘y = H_A + H_A∘σ`. -/
theorem cleared_pullback :
    ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * (GA_odeLHS.subst sympY)
      = Mp0 * dF 0 + Mp1 * dF 1 + Mp2 * dF 2 + Mp3 * dF 3 + Mp4 * dF 4 := by
  rw [subst_GA_odeLHS]
  rw [show ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7
        * ((c0Y.subst sympY) * Ffun 0 + (c1Y.subst sympY) * Ffun 1
            + (c2Y.subst sympY) * Ffun 2 + (c3Y.subst sympY) * Ffun 3
            + (c4Y.subst sympY) * Ffun 4)
      = ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c0Y.subst sympY) * Ffun 0)
        + ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c1Y.subst sympY) * Ffun 1)
        + ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c2Y.subst sympY) * Ffun 2)
        + ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c3Y.subst sympY) * Ffun 3)
        + ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * ((c4Y.subst sympY) * Ffun 4) by ring]
  rw [term0, term1, term2, term3, term4]
  rw [show dF 0 = Ffun 0 from dF_zero]
  simp only [Mp0, Mp1, Mp2, Mp3, Mp4, G1, G2, G3, G4, Ad]
  ring

end Submission.CDT
