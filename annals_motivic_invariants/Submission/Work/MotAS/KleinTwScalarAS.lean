import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwScalarASGuide
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.AsTransportSstage
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The scalar part of the AS link identity I1^AS (component `0`)

`kleinPAS`, `kleinRAS`, `kleinSecAS` are the Artin–Schreier (characteristic `5`) coordinates of the
quadro–cubic map `P^AS`, of its inverse `R^AS` and of the secant quintic `s^AS`
(`Submission/Work/MotAS/ASData.lean`).  The target is component `0` of the link identity

`R^AS (P^AS y) = s^AS(y) • y`   (characteristic `5`).

## Proof route

The AS coordinates are the images of the *split* (characteristic-free) Klein data of `Work.MotK`
under the Galois-coordinate substitution `x_i = Σ_j y_j (w+i)^j` with `w^5 = w + g`, reduced in the
algebra `R[w]/(w^5 - w - g)`.  All the transports needed are available:

* `MotAS.asTransportP`  : `P(asM w · y) = asN w · P^AS(y)`,
* `MotAS.asTransportR`  : `R(asN w · ẑ) = asM w · R^AS(ẑ)`,
* `MotAS.AsTransportSstage` : `s(asM w · y) = s^AS(y)`,
* `MotK.kleinR_kleinP`  : the split identity `R(P x) = s(x) • x`,
* `MotAS.asM_mulVec_injective` : `asM w` is invertible in characteristic `5`.

Applying the split identity to `x = asM w · y` and cancelling `asM w` gives the vector identity
**in any ring containing an element `w` with `w ^ 5 = w + g`**
(`KleinTwScalarAS_vec`).  The target ring need not contain such an `w`, so the identity is first
proved in the universal extension `AdjoinRoot (X^5 - X - g)` (where `w` is the class of `X`) and
then pushed back along the (injective) structure map `R → AdjoinRoot (X^5 - X - g)`
(`KleinTwScalarAS_map_*` are the naturality lemmas making this push-forward explicit).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Polynomial

namespace Work.MotAS

variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B]

/-- **The transported split identity.**  In any commutative ring containing an element `w` with
`w ^ 5 = w + g` (and with `5 = 0`), the AS coordinates satisfy `R^AS (P^AS y) = s^AS(y) • y`. -/
theorem KleinTwScalarAS_vec (a b g w : A) (h5 : (5 : A) = 0) (hw : w ^ 5 = w + g)
    (y : Fin 5 → A) :
    kleinRAS a b g (kleinPAS a b g y) = kleinSecAS a b g y • y := by
  have hX : (fun i => ∑ j, asM w i j * y j) = (asM w).mulVec y := by
    funext i
    rfl
  have hP : Work.MotK.kleinP a b ((asM w).mulVec y) = (asN w).mulVec (kleinPAS a b g y) := by
    rw [← hX]
    exact asTransportP a b g w h5 hw y
  have hS : Work.MotK.kleinSec a b ((asM w).mulVec y) = kleinSecAS a b g y := by
    rw [← hX]
    exact AsTransportSstage a b g w h5 hw y
  have hR : Work.MotK.kleinR a b ((asN w).mulVec (kleinPAS a b g y))
      = (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y)) :=
    asTransportR a b g w h5 hw (kleinPAS a b g y)
  have hsplit : Work.MotK.kleinR a b (Work.MotK.kleinP a b ((asM w).mulVec y))
      = Work.MotK.kleinSec a b ((asM w).mulVec y) • ((asM w).mulVec y) := by
    funext i
    simpa only [Pi.smul_apply, smul_eq_mul] using
      Work.MotK.kleinR_kleinP a b ((asM w).mulVec y) i
  have key : (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y))
      = (asM w).mulVec (kleinSecAS a b g y • y) := by
    rw [← hR, ← hP, hsplit, hS, Matrix.mulVec_smul]
  have hvec := asM_mulVec_injective h5 w key
  funext i
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hvec i

/-! ## Naturality of the AS coordinates under a ring hom

Every AS coordinate is a polynomial in `a, b, g, y` with integer coefficients, hence commutes with
any ring homomorphism `φ`.  Each statement is reduced to its literal indices, because `fin_cases`
produces `Fin` indices that the `Matrix.cons_val_*` lemmas do not recognise directly. -/

theorem KleinTwScalarAS_map_kleinPAS (φ : A →+* B) (a b g : A) (y : Fin 5 → A) :
    kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) = fun i => φ (kleinPAS a b g y i) := by
  funext i
  fin_cases i
  · change kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) 0 = φ (kleinPAS a b g y 0)
    simp only [kleinPAS, kleinPAS0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) 1 = φ (kleinPAS a b g y 1)
    simp only [kleinPAS, kleinPAS1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) 2 = φ (kleinPAS a b g y 2)
    simp only [kleinPAS, kleinPAS2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) 3 = φ (kleinPAS a b g y 3)
    simp only [kleinPAS, kleinPAS3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinPAS (φ a) (φ b) (φ g) (fun j => φ (y j)) 4 = φ (kleinPAS a b g y 4)
    simp only [kleinPAS, kleinPAS4, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring

theorem KleinTwScalarAS_map_kleinRAS (φ : A →+* B) (a b g : A) (z : Fin 5 → A) :
    kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) = fun i => φ (kleinRAS a b g z i) := by
  funext i
  fin_cases i
  · change kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) 0 = φ (kleinRAS a b g z 0)
    simp only [kleinRAS, kleinRAS0, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) 1 = φ (kleinRAS a b g z 1)
    simp only [kleinRAS, kleinRAS1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) 2 = φ (kleinRAS a b g z 2)
    simp only [kleinRAS, kleinRAS2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) 3 = φ (kleinRAS a b g z 3)
    simp only [kleinRAS, kleinRAS3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring
  · change kleinRAS (φ a) (φ b) (φ g) (fun j => φ (z j)) 4 = φ (kleinRAS a b g z 4)
    simp only [kleinRAS, kleinRAS4, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast] <;> ring

theorem KleinTwScalarAS_map_kleinSecAS (φ : A →+* B) (a b g : A) (y : Fin 5 → A) :
    kleinSecAS (φ a) (φ b) (φ g) (fun j => φ (y j)) = φ (kleinSecAS a b g y) := by
  simp only [kleinSecAS, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_natCast]
    <;> ring

/-- **I1^AS, component `0`.** -/
theorem KleinTwScalarAS {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) (h5 : (5 : R) = 0) :
    kleinRAS a b g (kleinPAS a b g y) 0 = y 0 * kleinSecAS a b g y := by
  by_cases hone : (1 : R) = 0
  · -- the trivial ring
    haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := ⟨0, 1, fun h => hone h.symm⟩
    -- the universal root `w` of `w ^ 5 - w - g`
    set p : Polynomial R := X ^ 5 - X - C g with hpdef
    have hpmonic : p.Monic := by
      rw [hpdef, show (X ^ 5 - X - C g : Polynomial R) = X ^ 5 - (X + C g) by ring]
      refine Polynomial.monic_X_pow_sub ?_
      calc ((X + C g : Polynomial R).degree)
          ≤ max (X : Polynomial R).degree (C g : Polynomial R).degree := Polynomial.degree_add_le _ _
        _ ≤ max (1 : WithBot ℕ) 0 := max_le_max Polynomial.degree_X_le Polynomial.degree_C_le
        _ = 1 := max_eq_left (WithBot.coe_le_coe.mpr (Nat.zero_le 1))
        _ < (5 : WithBot ℕ) := WithBot.coe_lt_coe.mpr (by norm_num)
    have hcoeff : p.coeff 5 = 1 := by
      rw [hpdef]
      simp [Polynomial.coeff_X_pow_self, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdeg5 : (5 : WithBot ℕ) ≤ p.degree :=
      Polynomial.le_degree_of_ne_zero (by rw [hcoeff]; exact hone)
    have hw : (AdjoinRoot.root p) ^ 5 = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by
      have h : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p - algebraMap R (AdjoinRoot p) g = 0 := by
        have h := AdjoinRoot.eval₂_root p
        simpa only [hpdef, AdjoinRoot.algebraMap_eq, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C] using h
      have h4 : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p = algebraMap R (AdjoinRoot p) g :=
        sub_eq_zero.mp h
      calc (AdjoinRoot.root p) ^ 5
          = ((AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p) + AdjoinRoot.root p :=
            (sub_add_cancel _ _).symm
        _ = algebraMap R (AdjoinRoot p) g + AdjoinRoot.root p := by rw [h4]
        _ = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by rw [add_comm]
    have h5A : (5 : AdjoinRoot p) = 0 := by
      have h' : algebraMap R (AdjoinRoot p) (5 : R) = 0 := by rw [h5, map_zero]
      rw [← map_ofNat (algebraMap R (AdjoinRoot p)) 5]
      exact h'
    -- injectivity of the structure map `R → R[X]/(X^5 - X - g)`
    have hinj : Function.Injective (algebraMap R (AdjoinRoot p)) := by
      intro x y hxy
      by_contra hne
      have hCz : Polynomial.C (x - y) ≠ 0 := Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hne)
      have hdeglt : (Polynomial.C (x - y)).degree < p.degree :=
        lt_of_le_of_lt (Polynomial.degree_C_le)
          (lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by norm_num : (0 : ℕ) < 5)) hdeg5)
      have hsub : algebraMap R (AdjoinRoot p) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hmk : AdjoinRoot.mk p (Polynomial.C (x - y)) = 0 := by
        rw [AdjoinRoot.mk_C]
        exact hsub
      rw [AdjoinRoot.mk_eq_zero] at hmk
      exact (hpmonic.not_dvd_of_degree_lt hCz hdeglt) hmk
    -- the identity in the universal extension
    have hmain := KleinTwScalarAS_vec (algebraMap R (AdjoinRoot p) a)
      (algebraMap R (AdjoinRoot p) b) (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p) h5A hw
      (fun j => algebraMap R (AdjoinRoot p) (y j))
    have h0 := congrFun hmain 0
    simp only [KleinTwScalarAS_map_kleinPAS, KleinTwScalarAS_map_kleinRAS,
      KleinTwScalarAS_map_kleinSecAS] at h0
    -- push the identity back along `R → AdjoinRoot p`
    apply hinj
    rw [map_mul]
    rw [mul_comm]
    simpa only [Pi.smul_apply, smul_eq_mul] using h0

end Work.MotAS
