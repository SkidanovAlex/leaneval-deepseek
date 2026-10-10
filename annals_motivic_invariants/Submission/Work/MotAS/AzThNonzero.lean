import Mathlib
import Submission.Work.MotAS.azThetaDefs
import Submission.Work.MotAS.AzThBricks
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary non-vanishing facts for the AS chart

This file collects the three non-vanishing facts used by `Work.MotAS.azTheta_fwVecAS2`
(the composite of the forward AS chart map with the inverse chart map), together with the
naturality of the AS Pfaffian map under ring homomorphisms:

* `map_kleinPAS` — `φ (kleinPAS a b g U j) = kleinPAS (φ a) (φ b) (φ g) (φ ∘ U) j`;
* `azZ_four_ne_zero` — the fourth component of `azZ = kleinRAS (azP)` does not vanish
  (`eval 0` gives `-g * (a²-ab-b²)²`);
* `azBilin_ne_zero` — the polar form `b(e₀, azZ)` does not vanish in characteristic `5`
  (`eval 0` gives `2*g*(a²-ab-b²)³`);
* `azSigma_ne_zero` — the target dual ruling quintic `kleinSecDualAS (azP)` at the plane does
  not vanish in characteristic `5`.  This is proved by splitting off the variable `X 0`
  (`MvPolynomial.finSuccEquiv K 1`): the coefficient of `X 0 ^ 5` is the constant
  `g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)`, which in characteristic `5` equals
  `g * (a² - ab - b²) ^ 5`, hence is non-zero under the hypotheses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS.AzTh

open MvPolynomial

/-! ## 1. Naturality of the AS Pfaffian map under a ring homomorphism -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_kleinPAS_0 (φ : R →+* S) (a b g : R) (U : Fin 5 → R) :
    φ (kleinPAS a b g U (0 : Fin 5))
      = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (0 : Fin 5) := by
  simp only [kleinPAS, kleinPAS0, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]

theorem map_kleinPAS_1 (φ : R →+* S) (a b g : R) (U : Fin 5 → R) :
    φ (kleinPAS a b g U (1 : Fin 5))
      = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (1 : Fin 5) := by
  simp only [kleinPAS, kleinPAS1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]

theorem map_kleinPAS_2 (φ : R →+* S) (a b g : R) (U : Fin 5 → R) :
    φ (kleinPAS a b g U (2 : Fin 5))
      = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (2 : Fin 5) := by
  simp only [kleinPAS, kleinPAS2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]

theorem map_kleinPAS_3 (φ : R →+* S) (a b g : R) (U : Fin 5 → R) :
    φ (kleinPAS a b g U (3 : Fin 5))
      = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (3 : Fin 5) := by
  simp only [kleinPAS, kleinPAS3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul, map_pow,
    map_ofNat, map_neg]

theorem map_kleinPAS_4 (φ : R →+* S) (a b g : R) (U : Fin 5 → R) :
    φ (kleinPAS a b g U (4 : Fin 5))
      = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (4 : Fin 5) := by
  simp only [kleinPAS, kleinPAS4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_add,
    map_sub, map_mul, map_pow, map_ofNat, map_neg]

/-- The AS Pfaffian map is natural in the coefficient ring. -/
theorem map_kleinPAS (φ : R →+* S) (a b g : R) (U : Fin 5 → R) (j : Fin 5) :
    φ (kleinPAS a b g U j) = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) j := by
  fin_cases j
  · show φ (kleinPAS a b g U (0 : Fin 5))
        = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (0 : Fin 5)
    exact map_kleinPAS_0 φ a b g U
  · show φ (kleinPAS a b g U (1 : Fin 5))
        = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (1 : Fin 5)
    exact map_kleinPAS_1 φ a b g U
  · show φ (kleinPAS a b g U (2 : Fin 5))
        = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (2 : Fin 5)
    exact map_kleinPAS_2 φ a b g U
  · show φ (kleinPAS a b g U (3 : Fin 5))
        = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (3 : Fin 5)
    exact map_kleinPAS_3 φ a b g U
  · show φ (kleinPAS a b g U (4 : Fin 5))
        = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (U i)) (4 : Fin 5)
    exact map_kleinPAS_4 φ a b g U

end Map

/-! ## 2. The chart quantities evaluated at the origin -/

section Origin

variable {K : Type*} [Field K]

/-- The fourth component of `azZ = R^AS (azP)` does not vanish: at the origin of the plane it
takes the value `-g * (a² - ab - b²)²`. -/
theorem azZ_four_ne_zero (a b g : K) (hg : g ≠ 0)
    (hA : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) : azZ a b g 4 ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.eval (fun _ : Fin 2 => (0 : K)) (azZ a b g 4) = 0 := by
    rw [h0, map_zero]
  have h2 : MvPolynomial.eval (fun _ : Fin 2 => (0 : K)) (azZ a b g 4)
      = -(g * (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(2:ℕ)) := by
    simp only [azZ, kleinRAS, kleinRAS4, azP, azPlane, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, map_one, map_zero,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    refl_ring1
  rw [h2] at h1
  exact mul_ne_zero hg (pow_ne_zero 2 hA) (neg_eq_zero.mp h1)

/-- The polar form `b(e₀, azZ)` does not vanish in characteristic `5`: at the origin of the plane
it takes the value `2 * g * (a² - ab - b²)³`. -/
theorem azBilin_ne_zero (h5 : (5 : K) = 0) (a b g : K) (hg : g ≠ 0)
    (hA : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g) ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.eval (fun _ : Fin 2 => (0 : K))
      (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g)) = 0 := by
    rw [h0, map_zero]
  have h2 : MvPolynomial.eval (fun _ : Fin 2 => (0 : K))
      (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g))
      = 2 * g * (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(3:ℕ) := by
    simp only [kleinBilinAS, kleinQAS, azZ, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3,
      kleinRAS4, azP, azPlane, Evec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Pi.add_apply, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, map_one, map_zero,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    refl_ring1
  rw [h2] at h1
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h := h5
    rw [show (5 : K) = 2 * 2 + 1 by norm_num, h2] at h
    norm_num at h
  exact mul_ne_zero (mul_ne_zero h2ne hg) (pow_ne_zero 3 hA) h1

end Origin

/-! ## 3. Non-vanishing of the target dual ruling quintic on the plane

`kleinSecDualAS` is a quintic form in `z`, and the only monomial of it containing `z 1 ^ 5` is
`g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10) * z 1 ^ 5`.  Splitting `K[X 0, X 1]` as a polynomial ring in
`X 0` over `K[X 1]` (`MvPolynomial.finSuccEquiv K 1`), the coefficient of `X 0 ^ 5` in
`kleinSecDualAS (C a) (C b) (C g) (azP K)` is therefore the constant
`g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)`, which is `g * (a² - ab - b²) ^ 5` in characteristic `5`.

The explicit expansion of that polynomial (below) was computed with a CAS from the on-disk
definition of `kleinSecDualAS`; the `simp only`/`ring` proof is a direct verification. -/

section Sigma

variable {K : Type*} [Field K]

/-- The explicit expansion of `kleinSecDualAS (C a) (C b) (C g) (azP K)` in `K[X 0, X 1]`. -/
theorem azSec_explicit (a b g : K) :
    kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K)
      = (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 0 ^(5:ℕ)
      + (-C a ^(9:ℕ) * C b + -C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ) * X 1
      + ((-2 : MvPolynomial (Fin 2) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C b ^(10:ℕ) * C g) * X 0 ^(3:ℕ)
      + ((2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ)) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(2:ℕ) * X 1
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 * X 1 ^(4:ℕ)
      + (C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 * X 1
      + (C a ^(10:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C a ^(4:ℕ) * C b ^(6:ℕ) * C g + C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 0
      + (C a ^(10:ℕ) * C g ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ) * C g ^(2:ℕ)) * X 1 ^(5:ℕ)
      + (C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 1 ^(3:ℕ)
      + (-C a ^(9:ℕ) * C b * C g + -C a ^(8:ℕ) * C b ^(2:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) * C g + C a ^(2:ℕ) * C b ^(8:ℕ) * C g + -C a * C b ^(9:ℕ) * C g) * X 1 ^(2:ℕ)
      + (-C a ^(10:ℕ) * C g ^(2:ℕ) + C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 2) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ) * C g ^(2:ℕ)) * X 1
      + (C a ^(10:ℕ) * C g ^(3:ℕ) + (2 : MvPolynomial (Fin 2) K) * C a ^(9:ℕ) * C b * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) * C g + -C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 2) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 2) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g ^(3:ℕ)) := by
  simp only [kleinSecDualAS, azP, azPlane, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  refl_ring1

/-- The coefficient of `X 0 ^ 5` in `kleinSecDualAS (C a) (C b) (C g) (azP K)`, as an element of
`K[X 1]` (`X 0` of the one-variable ring). -/
noncomputable def az5 (a b g : K) : MvPolynomial (Fin 1) K :=
  (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g)

/-- The coefficient of `X 0 ^ 3`. -/
noncomputable def az3 (a b g : K) : MvPolynomial (Fin 1) K :=
  (-C a ^(9:ℕ) * C b + -C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ)) * X 0 ^(1:ℕ)
      + ((-2 : MvPolynomial (Fin 1) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 1) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 1) K) * C b ^(10:ℕ) * C g)

/-- The coefficient of `X 0 ^ 2`. -/
noncomputable def az2 (a b g : K) : MvPolynomial (Fin 1) K :=
  ((2 : MvPolynomial (Fin 1) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ)
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(2:ℕ)
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(1:ℕ)

/-- The coefficient of `X 0 ^ 1`. -/
noncomputable def az1 (a b g : K) : MvPolynomial (Fin 1) K :=
  (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(4:ℕ)
      + (C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(1:ℕ)
      + (C a ^(10:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a ^(9:ℕ) * C b * C g + (-2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C a ^(4:ℕ) * C b ^(6:ℕ) * C g + C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g)

/-- The coefficient of `X 0 ^ 0`. -/
noncomputable def az0 (a b g : K) : MvPolynomial (Fin 1) K :=
  (C a ^(10:ℕ) * C g ^(2:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ) * C g ^(2:ℕ)) * X 0 ^(5:ℕ)
      + (C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ)
      + (-C a ^(9:ℕ) * C b * C g + -C a ^(8:ℕ) * C b ^(2:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a ^(7:ℕ) * C b ^(3:ℕ) * C g + (2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a ^(3:ℕ) * C b ^(7:ℕ) * C g + C a ^(2:ℕ) * C b ^(8:ℕ) * C g + -C a * C b ^(9:ℕ) * C g) * X 0 ^(2:ℕ)
      + (-C a ^(10:ℕ) * C g ^(2:ℕ) + C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 1) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ) * C g ^(2:ℕ)) * X 0 ^(1:ℕ)
      + (C a ^(10:ℕ) * C g ^(3:ℕ) + (2 : MvPolynomial (Fin 1) K) * C a ^(9:ℕ) * C b * C g + (2 : MvPolynomial (Fin 1) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) * C g + -C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 1) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 1) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g ^(3:ℕ))

/-- The part of `kleinSecDualAS (azP)` of `X 0`-degree at most `4`. -/
noncomputable def azLow (a b g : K) : Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.C (az3 a b g) * Polynomial.X ^(3:ℕ) + Polynomial.C (az2 a b g) * Polynomial.X ^(2:ℕ)
    + Polynomial.C (az1 a b g) * Polynomial.X ^(1:ℕ) + Polynomial.C (az0 a b g)

/-- `finSuccEquiv` sends constants to constants. -/
theorem azFinSuccEquiv_C (r : K) :
    MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C r)
      = Polynomial.C (MvPolynomial.C r) := by
  rw [← MvPolynomial.algebraMap_eq K (Fin 2), AlgEquiv.commutes, Polynomial.algebraMap_apply]
  rfl

/-- `finSuccEquiv` sends `X 1` to the constant polynomial `X 0`. -/
theorem azFinSuccEquiv_X_1 :
    MvPolynomial.finSuccEquiv K 1 (X 1 : MvPolynomial (Fin 2) K)
      = Polynomial.C (X 0 : MvPolynomial (Fin 1) K) := by
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]

/-- **The `X 0`-decomposition of `kleinSecDualAS (azP)`.** -/
theorem azSec_succEquiv (a b g : K) :
    MvPolynomial.finSuccEquiv K 1
        (kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K))
      = Polynomial.C (az5 a b g) * Polynomial.X ^(5:ℕ) + azLow a b g := by
  rw [azSec_explicit]
  simp only [azLow, az5, az3, az2, az1, az0,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    MvPolynomial.finSuccEquiv_X_zero, azFinSuccEquiv_X_1, azFinSuccEquiv_C,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat]
  refl_ring1

/-- The lower part has `X`-degree at most `4`. -/
theorem azLow_natDegree_le (a b g : K) : (azLow a b g).natDegree ≤ 4 := by
  rw [azLow, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have h3 : ¬ (m = 3) := by omega
  have h2 : ¬ (m = 2) := by omega
  have h1 : ¬ (m = 1) := by omega
  have h0 : ¬ (m = 0) := by omega
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C,
    if_neg h3, if_neg h2, if_neg h1, if_neg h0]
  refl_ring1

/-- The top coefficient `az5` is the constant `g * (a ^ 10 - a ^ 5 * b ^ 5 - b ^ 10)`. -/
theorem az5_eq (a b g : K) :
    az5 a b g = MvPolynomial.C (g * (a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ))) := by
  rw [az5]
  simp only [← map_pow, ← map_mul, ← map_add, ← map_neg]
  congr 1
  refl_ring1

/-- The coefficient of `X 0 ^ 5`. -/
theorem azSec_coeff5 (a b g : K) :
    (MvPolynomial.finSuccEquiv K 1
        (kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K))).coeff 5
      = az5 a b g := by
  rw [azSec_succEquiv a b g, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  have hl : (azLow a b g).natDegree < 5 := by
    have := azLow_natDegree_le a b g
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl]
  simp

/-- In characteristic `5` the top coefficient is `g * (a² - ab - b²) ^ 5 ≠ 0`. -/
theorem az5_ne_zero (h5 : (5 : K) = 0) (a b g : K) (hg : g ≠ 0)
    (hA : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) : az5 a b g ≠ 0 := by
  have hpow : (a ^(2:ℕ) - a * b - b ^(2:ℕ)) ^(5:ℕ) = a ^(10:ℕ) - a ^(5:ℕ) * b ^(5:ℕ) - b ^(10:ℕ) := by
    linear_combination (norm := refl_ring1 (mod := 5))
  rw [az5_eq]
  intro h0
  rw [MvPolynomial.C_eq_zero] at h0
  rw [← hpow] at h0
  exact mul_ne_zero hg (pow_ne_zero 5 hA) h0

/-- **The target dual ruling quintic does not vanish on the plane** (characteristic `5`). -/
theorem azSigma_ne_zero (h5 : (5 : K) = 0) (a b g : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hg : g ≠ 0) (hA : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) :
    kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K) ≠ 0 := by
  intro h0
  have h1 : MvPolynomial.finSuccEquiv K 1
      (kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (azP K)) = 0 := by
    rw [h0, map_zero]
  have h2 := azSec_coeff5 (K := K) a b g
  rw [h1, Polynomial.coeff_zero] at h2
  exact az5_ne_zero h5 a b g hg hA h2.symm

end Sigma

end Work.MotAS.AzTh
