/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.PhiSDefs
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZPhiMemGen` — the AS projection lands in the residual ideal

The target is

`kleinRAS a b g (phiAS a b · y) k ∈ √⟨kleinPAS a b (3g) y i⟩_i`

for every commutative ring `R` with `5 = 0` and every `k`.  In fact the *ideal* membership holds
(the radical is only what was asked for); the same argument proves the `Ideal.span` version, which
is `Work.MotAS.asPhi_mem`.

## Strategy

Everything is an explicit polynomial identity with **integer** coefficients, so it is proved
directly in the given ring `R` (no universal ring and no transfer are needed):

* `zR a b y` is the argument `phiAS · y` written out componentwise, and `zR_eq` identifies it with
  `fun i => ∑ j, phiAS a b i j * y j`;
* `cofR a b g y k i` are the explicit cofactors of the certificate, i.e. the polynomials with
  integer coefficients such that
  `kleinRAS a b g (zR a b y) k = ∑ i, cofR a b g y k i * kleinPAS a b (3g) y i`
  holds **modulo `5`**; its `5`-adic defect is the explicit polynomial `rRk`:
  `kleinRAS a b g (zR a b y) k - ∑ i, … = 5 * rRk a b g y`.
* The certificate `certR` is then the integer identity above (verified by `ring`, which is a
  characteristic-free computation), followed by `5 = 0`.

The cofactors and the five residuals `rR0 … rR4` were computed with the sympy/GF(5) linear-algebra
script `_asz/solve3.py` plus `_asz/parse_qM.py` (the cofactors have `a`/`b`-degree `5`,
`g`-degree `≤ 1`, `y`-degree `1` and `142` nonzero terms in total; the residuals have `86`–`130`
terms each).

## A remark on `ring` and characteristic `5`

The identity holds only in characteristic `5`, so it is *not* an identity over `ℤ`; proving it by
`ring` inside a ring of characteristic `5` fails, because `ring` compares the (integer) coefficients
of the two normal forms.  Passing through the explicit `5`-adic defect keeps every `ring` call a
characteristic-free identity, which is why the residuals are carried.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.MotC5N3

open Work.MotAS

/-! ## `phiAS` in matrix form

`phiAS` is defined by a `match` on the two index values, which `simp` will not reduce; the matrix
form `phiASM` below *is* reducible, and the two agree pointwise (`phiAS_eq_phiASM`, by `rfl` after
`fin_cases`). -/

/-- The matrix form of `phiAS` (`Phi5 = D⁻¹ p(T₁)`). -/
private def phiASM {R : Type*} [CommRing R] (a b : R) : Fin 5 → Fin 5 → R :=
  ![![0, 3 * a + b, 0, 3 * a + 4 * b, 0],
    ![0, 0, 3 * a + b, 0, a + 3 * b],
    ![0, 0, 0, a + 2 * b, 0],
    ![0, 0, 0, 0, 4 * a + 3 * b],
    ![0, 0, 0, 0, 0]]

/-- `phiAS` and its matrix form agree. -/
private lemma phiAS_eq_phiASM {R : Type*} [CommRing R] (a b : R) (k j : Fin 5) :
    phiAS a b k j = phiASM a b k j := by
  fin_cases k <;> fin_cases j <;> rfl

/-! ## The argument `z = phiAS · y`, componentwise -/

/-- `phiAS · y`, written out so that the components reduce definitionally. -/
private def zR {R : Type*} [CommRing R] (a b : R) (y : Fin 5 → R) : Fin 5 → R :=
  ![(3 * a + b) * y 1 + (3 * a + 4 * b) * y 3,
    (3 * a + b) * y 2 + (a + 3 * b) * y 4,
    (a + 2 * b) * y 3,
    (4 * a + 3 * b) * y 4,
    0]

/-- `zR` is `fun i => ∑ j, phiAS a b i j * y j`. -/
private lemma zR_eq {R : Type*} [CommRing R] (a b : R) (y : Fin 5 → R) :
    zR a b y = fun i => ∑ j, phiAS a b i j * y j := by
  funext i
  fin_cases i
  · change zR a b y (0 : Fin 5) = ∑ j : Fin 5, phiAS a b (0 : Fin 5) j * y j
    simp only [zR, phiAS_eq_phiASM, phiASM, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_five]
    refl_ring1
  · change zR a b y (1 : Fin 5) = ∑ j : Fin 5, phiAS a b (1 : Fin 5) j * y j
    simp only [zR, phiAS_eq_phiASM, phiASM, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_five]
    refl_ring1
  · change zR a b y (2 : Fin 5) = ∑ j : Fin 5, phiAS a b (2 : Fin 5) j * y j
    simp only [zR, phiAS_eq_phiASM, phiASM, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_five]
    refl_ring1
  · change zR a b y (3 : Fin 5) = ∑ j : Fin 5, phiAS a b (3 : Fin 5) j * y j
    simp only [zR, phiAS_eq_phiASM, phiASM, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_five]
    refl_ring1
  · change zR a b y (4 : Fin 5) = ∑ j : Fin 5, phiAS a b (4 : Fin 5) j * y j
    simp only [zR, phiAS_eq_phiASM, phiASM, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Fin.sum_univ_five]
    refl_ring1

/-! ## The cofactors and the five `5`-adic defects -/

/-- The explicit cofactors of the certificate (integer coefficients, reduced modulo `5` to
`±1, ±2`). -/
private def cofR {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : Fin 5 → Fin 5 → R :=
  ![![((0 : R)), (-b ^(5:ℕ) * y 2 + a * b ^(4:ℕ) * y 4 + -a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (2 : R) * a ^(5:ℕ) * y 2 + (-2 : R) * a ^(5:ℕ) * y 4), (b ^(5:ℕ) * y 1 + (-2 : R) * b ^(5:ℕ) * y 3 + -a * b ^(4:ℕ) * y 3 + -a ^(2:ℕ) * b ^(3:ℕ) * y 3 + a ^(3:ℕ) * b ^(2:ℕ) * y 3 + a ^(4:ℕ) * b * y 3 + (-2 : R) * a ^(5:ℕ) * y 1 + (2 : R) * a ^(5:ℕ) * y 3), (b ^(5:ℕ) * y 4 + (-2 : R) * a * b ^(4:ℕ) * y 2 + a * b ^(4:ℕ) * y 4 + -a ^(2:ℕ) * b ^(3:ℕ) * y 4 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 2 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (2 : R) * a ^(4:ℕ) * b * y 4 + -a ^(5:ℕ) * y 2 + a ^(5:ℕ) * y 4), (-b ^(5:ℕ) * y 1 + b ^(5:ℕ) * y 3 + (2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 1 + (-2 : R) * a ^(4:ℕ) * b * y 1)],
    ![((2 : R) * b ^(5:ℕ) * y 4 + a * b ^(4:ℕ) * y 4 + -a ^(2:ℕ) * b ^(3:ℕ) * y 4 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (2 : R) * a ^(4:ℕ) * b * y 4 + a ^(5:ℕ) * y 4), (b ^(5:ℕ) * y 3 + (-2 : R) * a ^(5:ℕ) * y 3), ((-2 : R) * b ^(5:ℕ) * y 2 + -b ^(5:ℕ) * y 4 + -a * b ^(4:ℕ) * y 2 + a ^(2:ℕ) * b ^(3:ℕ) * y 2 + -a ^(2:ℕ) * b ^(3:ℕ) * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 2 + (-2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (-2 : R) * a ^(4:ℕ) * b * y 2 + -a ^(5:ℕ) * y 2 + (-2 : R) * a ^(5:ℕ) * y 4), ((-2 : R) * b ^(5:ℕ) * y 3 + (-2 : R) * a * b ^(4:ℕ) * y 1 + (2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 1 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 3 + a ^(3:ℕ) * b ^(2:ℕ) * y 1 + a ^(3:ℕ) * b ^(2:ℕ) * y 3 + a ^(4:ℕ) * b * y 1 + a ^(5:ℕ) * y 3), (-b ^(5:ℕ) * y 0 + (2 : R) * a * b ^(4:ℕ) * y 0 + (-2 : R) * a * b ^(4:ℕ) * y 2 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 0 + -a ^(2:ℕ) * b ^(3:ℕ) * y 2 + -a ^(3:ℕ) * b ^(2:ℕ) * y 0 + (-2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 2 + -a ^(4:ℕ) * b * y 0 + -a ^(4:ℕ) * b * y 2 + (2 : R) * a ^(5:ℕ) * y 0)],
    ![((0 : R)), (b ^(5:ℕ) * y 4 + (-2 : R) * a ^(5:ℕ) * y 4), ((-2 : R) * b ^(5:ℕ) * y 3 + -a ^(5:ℕ) * y 3), ((2 : R) * b ^(5:ℕ) * y 2 + -b ^(5:ℕ) * y 4 + a * b ^(4:ℕ) * y 4 + (2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 4 + -a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (-2 : R) * a ^(4:ℕ) * b * y 4 + a ^(5:ℕ) * y 2 + (-2 : R) * a ^(5:ℕ) * y 4), (-b ^(5:ℕ) * y 1 + (2 : R) * a ^(5:ℕ) * y 1)],
    ![((-2 : R) * b ^(5:ℕ) * y 4 + (2 : R) * a * b ^(4:ℕ) * y 4 + -a ^(2:ℕ) * b ^(3:ℕ) * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 4 + a ^(4:ℕ) * b * y 4 + a ^(5:ℕ) * y 4), ((0 : R)), ((2 : R) * b ^(5:ℕ) * y 2 + b ^(5:ℕ) * y 4 + (-2 : R) * a * b ^(4:ℕ) * y 2 + a * b ^(4:ℕ) * y 4 + a ^(2:ℕ) * b ^(3:ℕ) * y 2 + -a ^(2:ℕ) * b ^(3:ℕ) * y 4 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 2 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 4 + -a ^(4:ℕ) * b * y 2 + (2 : R) * a ^(4:ℕ) * b * y 4 + -a ^(5:ℕ) * y 2 + (-2 : R) * a ^(5:ℕ) * y 4), (-b ^(5:ℕ) * y 1 + -b ^(5:ℕ) * y 3 + a * b ^(4:ℕ) * y 1 + (2 : R) * a * b ^(4:ℕ) * y 3 + (2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 1 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 3 + -a ^(3:ℕ) * b ^(2:ℕ) * y 1 + -a ^(3:ℕ) * b ^(2:ℕ) * y 3 + (-2 : R) * a ^(4:ℕ) * b * y 1 + -a ^(4:ℕ) * b * y 3 + (-2 : R) * a ^(5:ℕ) * y 1 + (2 : R) * a ^(5:ℕ) * y 3), (b ^(5:ℕ) * y 0 + -a * b ^(4:ℕ) * y 0 + (2 : R) * a * b ^(4:ℕ) * y 2 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 0 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 2 + a ^(3:ℕ) * b ^(2:ℕ) * y 0 + -a ^(3:ℕ) * b ^(2:ℕ) * y 2 + (2 : R) * a ^(4:ℕ) * b * y 0 + -a ^(4:ℕ) * b * y 2 + (2 : R) * a ^(5:ℕ) * y 0)],
    ![((0 : R)), (b ^(5:ℕ) * y 4 + a * b ^(4:ℕ) * y 4 + (-2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 4 + -a ^(3:ℕ) * b ^(2:ℕ) * y 4 + (2 : R) * a ^(4:ℕ) * b * y 4 + (-2 : R) * a ^(5:ℕ) * y 4), ((2 : R) * b ^(5:ℕ) * y 3 + (2 : R) * a * b ^(4:ℕ) * y 3 + a ^(2:ℕ) * b ^(3:ℕ) * y 3 + (-2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 3 + -a ^(4:ℕ) * b * y 3 + a ^(5:ℕ) * y 3), ((-2 : R) * b ^(5:ℕ) * y 2 + (-2 : R) * b ^(5:ℕ) * y 4 + (-2 : R) * a * b ^(4:ℕ) * y 2 + -a ^(2:ℕ) * b ^(3:ℕ) * y 2 + (2 : R) * a ^(3:ℕ) * b ^(2:ℕ) * y 2 + a ^(4:ℕ) * b * y 2 + -a ^(5:ℕ) * y 2), (-b ^(5:ℕ) * y 1 + (2 : R) * b ^(5:ℕ) * y 3 + -a * b ^(4:ℕ) * y 1 + (2 : R) * a ^(2:ℕ) * b ^(3:ℕ) * y 1 + a ^(3:ℕ) * b ^(2:ℕ) * y 1 + (-2 : R) * a ^(4:ℕ) * b * y 1 + (2 : R) * a ^(5:ℕ) * y 1)]]

/-- The `5`-adic defect of component `0`. -/
private def rR0 {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  (6 : R) * b ^(7:ℕ) * g * y 4 * y 4 * y 4 + (-9 : R) * a * b ^(6:ℕ) * g * y 4 * y 4 * y 4 + (-60 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 4 * y 4 * y 4 + (-55 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 4 * y 4 * y 4 + (28 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 4 * y 4 * y 4 + (91 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 4 * y 4 * y 4 + (75 : R) * a ^(6:ℕ) * b * g * y 4 * y 4 * y 4 + (19 : R) * a ^(7:ℕ) * g * y 4 * y 4 * y 4 + (28 : R) * b ^(7:ℕ) * y 3 * y 4 * y 4 + (77 : R) * a * b ^(6:ℕ) * y 3 * y 4 * y 4 + (64 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 4 * y 4 + (15 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 4 * y 4 + (-5 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 4 * y 4 + (-5 : R) * a ^(6:ℕ) * b * y 3 * y 4 * y 4 + (-5 : R) * a ^(7:ℕ) * y 3 * y 4 * y 4 + (-13 : R) * a * b ^(6:ℕ) * g * y 3 * y 3 * y 4 + (-25 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 3 * y 3 * y 4 + (2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 3 * y 4 + (37 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 3 * y 4 + (17 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 3 * y 4 + (-5 : R) * a ^(6:ℕ) * b * g * y 3 * y 3 * y 4 + (-4 : R) * a ^(7:ℕ) * g * y 3 * y 3 * y 4 + (-28 : R) * b ^(7:ℕ) * y 3 * y 3 * y 3 + (-89 : R) * a * b ^(6:ℕ) * y 3 * y 3 * y 3 + (-96 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 3 * y 3 + (-23 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 3 * y 3 + (31 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 3 * y 3 + (19 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 3 * y 3 + -a ^(6:ℕ) * b * y 3 * y 3 * y 3 + (-2 : R) * a ^(7:ℕ) * y 3 * y 3 * y 3 + (3 : R) * b ^(7:ℕ) * g * y 2 * y 4 * y 4 + (6 : R) * a * b ^(6:ℕ) * g * y 2 * y 4 * y 4 + (-41 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 4 * y 4 + (-98 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 4 * y 4 + (-56 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 4 * y 4 + (27 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 2 * y 4 * y 4 + (57 : R) * a ^(6:ℕ) * b * g * y 2 * y 4 * y 4 + (33 : R) * a ^(7:ℕ) * g * y 2 * y 4 * y 4 + (9 : R) * b ^(7:ℕ) * y 2 * y 3 * y 4 + (50 : R) * a * b ^(6:ℕ) * y 2 * y 3 * y 4 + (76 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 3 * y 4 + (45 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 3 * y 4 + (11 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 3 * y 4 + (12 : R) * a ^(6:ℕ) * b * y 2 * y 3 * y 4 + (11 : R) * a ^(7:ℕ) * y 2 * y 3 * y 4 + b ^(7:ℕ) * g * y 2 * y 3 * y 3 + (5 : R) * a * b ^(6:ℕ) * g * y 2 * y 3 * y 3 + a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 3 * y 3 + (-7 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 3 * y 3 + -a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 3 * y 3 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 2 * y 3 * y 3 + (7 : R) * a ^(6:ℕ) * b * g * y 2 * y 3 * y 3 + (7 : R) * a * b ^(6:ℕ) * g * y 2 * y 2 * y 4 + (16 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 2 * y 4 + (-4 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 2 * y 4 + (-22 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 2 * y 4 + (7 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 2 * y 2 * y 4 + (30 : R) * a ^(6:ℕ) * b * g * y 2 * y 2 * y 4 + (12 : R) * a ^(7:ℕ) * g * y 2 * y 2 * y 4 + (2 : R) * b ^(7:ℕ) * y 2 * y 2 * y 3 + (6 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 3 + (17 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 3 + (17 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 3 + (10 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 3 + (4 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 3 + (-5 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 3 + (-6 : R) * a ^(7:ℕ) * y 2 * y 2 * y 3 + (7 : R) * b ^(7:ℕ) * y 1 * y 4 * y 4 + (37 : R) * a * b ^(6:ℕ) * y 1 * y 4 * y 4 + (58 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 4 * y 4 + (28 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 4 * y 4 + -a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 4 * y 4 + (-8 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 4 * y 4 + (-4 : R) * a ^(6:ℕ) * b * y 1 * y 4 * y 4 + (-6 : R) * a ^(7:ℕ) * y 1 * y 4 * y 4 + (-7 : R) * a * b ^(6:ℕ) * g * y 1 * y 3 * y 4 + (-19 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 1 * y 3 * y 4 + (-9 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 1 * y 3 * y 4 + (13 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 1 * y 3 * y 4 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 1 * y 3 * y 4 + (-5 : R) * a ^(6:ℕ) * b * g * y 1 * y 3 * y 4 + (-17 : R) * b ^(7:ℕ) * y 1 * y 3 * y 3 + (-97 : R) * a * b ^(6:ℕ) * y 1 * y 3 * y 3 + (-175 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 3 * y 3 + (-88 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 3 * y 3 + (59 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 3 * y 3 + (63 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 3 * y 3 + (-2 : R) * a ^(6:ℕ) * b * y 1 * y 3 * y 3 + (-10 : R) * a ^(7:ℕ) * y 1 * y 3 * y 3 + (3 : R) * b ^(7:ℕ) * y 1 * y 2 * y 4 + (19 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 4 + (45 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 4 + (42 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 4 + (16 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 4 + (6 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 4 + (4 : R) * a ^(6:ℕ) * b * y 1 * y 2 * y 4 + (11 : R) * a ^(7:ℕ) * y 1 * y 2 * y 4 + a * b ^(6:ℕ) * y 1 * y 2 * y 2 + (7 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 2 + (13 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 2 + (7 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 2 + (2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 2 + (-5 : R) * a ^(7:ℕ) * y 1 * y 2 * y 2 + (-4 : R) * b ^(7:ℕ) * y 1 * y 1 * y 3 + (-28 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 3 + (-76 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 3 + (-73 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 3 + (21 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 3 + (60 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 3 + (7 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 3 + (-13 : R) * a ^(7:ℕ) * y 1 * y 1 * y 3 + (-2 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 1 + (-9 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 1 + (-14 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 1 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 1 + (14 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 1 + (5 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 1 + (-5 : R) * a ^(7:ℕ) * y 1 * y 1 * y 1 + a * b ^(6:ℕ) * y 0 * y 3 * y 4 + (-2 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 3 * y 4 + (2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 3 * y 4 + a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 3 * y 4 + -b ^(7:ℕ) * y 0 * y 2 * y 3 + (-2 : R) * a * b ^(6:ℕ) * y 0 * y 2 * y 3 + -a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 2 * y 3 + (2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 2 * y 3 + (2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 2 * y 3 + (2 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 1 * y 4 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 1 * y 4 + (-2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 1 * y 4

private def rR1 {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  (11 : R) * a * b ^(6:ℕ) * y 4 * y 4 * y 4 + (31 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 4 * y 4 * y 4 + (39 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 4 * y 4 * y 4 + (15 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 4 * y 4 * y 4 + (4 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 4 * y 4 * y 4 + (23 : R) * a ^(6:ℕ) * b * y 4 * y 4 * y 4 + (14 : R) * a ^(7:ℕ) * y 4 * y 4 * y 4 + (15 : R) * b ^(7:ℕ) * g * y 3 * y 4 * y 4 + (54 : R) * a * b ^(6:ℕ) * g * y 3 * y 4 * y 4 + (44 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 3 * y 4 * y 4 + (-15 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 4 * y 4 + (12 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 4 * y 4 + (56 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 4 * y 4 + (42 : R) * a ^(6:ℕ) * b * g * y 3 * y 4 * y 4 + (12 : R) * a ^(7:ℕ) * g * y 3 * y 4 * y 4 + (25 : R) * b ^(7:ℕ) * y 3 * y 3 * y 4 + (38 : R) * a * b ^(6:ℕ) * y 3 * y 3 * y 4 + (-4 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 3 * y 4 + (-42 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 3 * y 4 + (-5 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 3 * y 4 + (54 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 3 * y 4 + (53 : R) * a ^(6:ℕ) * b * y 3 * y 3 * y 4 + (14 : R) * a ^(7:ℕ) * y 3 * y 3 * y 4 + -b ^(7:ℕ) * g * y 3 * y 3 * y 3 + (-5 : R) * a * b ^(6:ℕ) * g * y 3 * y 3 * y 3 + (-5 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 3 * y 3 * y 3 + (3 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 3 * y 3 + (4 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 3 * y 3 + -a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 3 * y 3 + (-2 : R) * a ^(6:ℕ) * b * g * y 3 * y 3 * y 3 + a ^(7:ℕ) * g * y 3 * y 3 * y 3 + (-3 : R) * a * b ^(6:ℕ) * y 2 * y 4 * y 4 + (-14 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 4 * y 4 + (-30 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 4 * y 4 + (-26 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 4 * y 4 + (-24 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 4 * y 4 + (-12 : R) * a ^(6:ℕ) * b * y 2 * y 4 * y 4 + (3 : R) * a ^(7:ℕ) * y 2 * y 4 * y 4 + (-7 : R) * a * b ^(6:ℕ) * g * y 2 * y 3 * y 4 + (-19 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 3 * y 4 + (-9 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 3 * y 4 + (13 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 3 * y 4 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 2 * y 3 * y 4 + (-5 : R) * a ^(6:ℕ) * b * g * y 2 * y 3 * y 4 + (7 : R) * b ^(7:ℕ) * y 2 * y 3 * y 3 + (29 : R) * a * b ^(6:ℕ) * y 2 * y 3 * y 3 + (14 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 3 * y 3 + (-36 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 3 * y 3 + (-25 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 3 * y 3 + (33 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 3 * y 3 + (38 : R) * a ^(6:ℕ) * b * y 2 * y 3 * y 3 + (11 : R) * a ^(7:ℕ) * y 2 * y 3 * y 3 + (2 : R) * b ^(7:ℕ) * y 2 * y 2 * y 4 + (9 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 4 + (20 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 4 + (14 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 4 + (-5 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 4 + (-9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 4 + (-25 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 4 + (-12 : R) * a ^(7:ℕ) * y 2 * y 2 * y 4 + b ^(7:ℕ) * y 2 * y 2 * y 2 + (2 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 2 + (7 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 2 + (12 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 2 + (7 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 2 + (5 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 2 + a ^(6:ℕ) * b * y 2 * y 2 * y 2 + (-5 : R) * a ^(7:ℕ) * y 2 * y 2 * y 2 + (6 : R) * b ^(7:ℕ) * g * y 1 * y 4 * y 4 + (21 : R) * a * b ^(6:ℕ) * g * y 1 * y 4 * y 4 + (19 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 1 * y 4 * y 4 + (-14 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 1 * y 4 * y 4 + (-25 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 1 * y 4 * y 4 + (20 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 1 * y 4 * y 4 + (43 : R) * a ^(6:ℕ) * b * g * y 1 * y 4 * y 4 + (18 : R) * a ^(7:ℕ) * g * y 1 * y 4 * y 4 + (7 : R) * b ^(7:ℕ) * y 1 * y 3 * y 4 + (20 : R) * a * b ^(6:ℕ) * y 1 * y 3 * y 4 + (-27 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 3 * y 4 + (-76 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 3 * y 4 + (-39 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 3 * y 4 + (38 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 3 * y 4 + (68 : R) * a ^(6:ℕ) * b * y 1 * y 3 * y 4 + (27 : R) * a ^(7:ℕ) * y 1 * y 3 * y 4 + (2 : R) * b ^(7:ℕ) * y 1 * y 2 * y 3 + (18 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 3 + (28 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 3 + (-21 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 3 + (-39 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 3 + (23 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 3 + (55 : R) * a ^(6:ℕ) * b * y 1 * y 2 * y 3 + (22 : R) * a ^(7:ℕ) * y 1 * y 2 * y 3 + (2 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 4 + (-7 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 4 + (-29 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 4 + (-22 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 4 + (4 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 4 + (17 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 4 + (11 : R) * a ^(7:ℕ) * y 1 * y 1 * y 4 + (2 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 2 + (9 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 2 + (4 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 2 + (-15 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 2 + (-2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 2 + (16 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 2 + (11 : R) * a ^(7:ℕ) * y 1 * y 1 * y 2 + a * b ^(6:ℕ) * y 0 * y 4 * y 4 + (-2 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 4 * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 4 * y 4 + a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 4 * y 4 + -a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 4 * y 4 + (-2 : R) * a ^(7:ℕ) * y 0 * y 4 * y 4 + -b ^(7:ℕ) * y 0 * y 3 * y 3 + -a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 3 * y 3 + (-2 : R) * a * b ^(6:ℕ) * y 0 * y 2 * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 2 * y 4 + -b ^(7:ℕ) * y 0 * y 2 * y 2 + -a * b ^(6:ℕ) * y 0 * y 2 * y 2 + a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 2 * y 2 + -a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 2 * y 2 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 2 * y 2 + a ^(6:ℕ) * b * y 0 * y 2 * y 2 + a * b ^(6:ℕ) * y 0 * y 0 * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 0 * y 4 + a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 0 * y 4 + a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 0 * y 4 + a ^(6:ℕ) * b * y 0 * y 0 * y 4 + -a ^(7:ℕ) * y 0 * y 0 * y 4

private def rR2 {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  (-27 : R) * a * b ^(6:ℕ) * g * y 4 * y 4 * y 4 + (-96 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 4 * y 4 * y 4 + (-129 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 4 * y 4 * y 4 + (-66 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 4 * y 4 * y 4 + (23 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 4 * y 4 * y 4 + (64 : R) * a ^(6:ℕ) * b * g * y 4 * y 4 * y 4 + (32 : R) * a ^(7:ℕ) * g * y 4 * y 4 * y 4 + (-18 : R) * b ^(7:ℕ) * y 3 * y 4 * y 4 + (-83 : R) * a * b ^(6:ℕ) * y 3 * y 4 * y 4 + (-116 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 4 * y 4 + (-78 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 4 * y 4 + (-8 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 4 * y 4 + (36 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 4 * y 4 + (19 : R) * a ^(6:ℕ) * b * y 3 * y 4 * y 4 + (-2 : R) * a ^(7:ℕ) * y 3 * y 4 * y 4 + (3 : R) * b ^(7:ℕ) * g * y 3 * y 3 * y 4 + (7 : R) * a * b ^(6:ℕ) * g * y 3 * y 3 * y 4 + -a ^(2:ℕ) * b ^(5:ℕ) * g * y 3 * y 3 * y 4 + (-11 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 3 * y 4 + (2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 3 * y 4 + (11 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 3 * y 4 + (6 : R) * a ^(6:ℕ) * b * g * y 3 * y 3 * y 4 + (4 : R) * a ^(7:ℕ) * g * y 3 * y 3 * y 4 + (10 : R) * b ^(7:ℕ) * y 3 * y 3 * y 3 + (14 : R) * a * b ^(6:ℕ) * y 3 * y 3 * y 3 + (-10 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 3 * y 3 + (-22 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 3 * y 3 + (5 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 3 * y 3 + (26 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 3 * y 3 + (16 : R) * a ^(6:ℕ) * b * y 3 * y 3 * y 3 + (3 : R) * a ^(7:ℕ) * y 3 * y 3 * y 3 + (6 : R) * b ^(7:ℕ) * g * y 2 * y 4 * y 4 + (21 : R) * a * b ^(6:ℕ) * g * y 2 * y 4 * y 4 + (19 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 4 * y 4 + (-17 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 4 * y 4 + (-31 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 4 * y 4 + (17 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 2 * y 4 * y 4 + (43 : R) * a ^(6:ℕ) * b * g * y 2 * y 4 * y 4 + (21 : R) * a ^(7:ℕ) * g * y 2 * y 4 * y 4 + (-11 : R) * a * b ^(6:ℕ) * y 2 * y 3 * y 4 + (-73 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 3 * y 4 + (-100 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 3 * y 4 + (-28 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 3 * y 4 + (60 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 3 * y 4 + (54 : R) * a ^(6:ℕ) * b * y 2 * y 3 * y 4 + (14 : R) * a ^(7:ℕ) * y 2 * y 3 * y 4 + (2 : R) * b ^(7:ℕ) * y 2 * y 2 * y 3 + (4 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 3 + a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 3 + (-24 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 3 + (-28 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 3 + (7 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 3 + (33 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 3 + (15 : R) * a ^(7:ℕ) * y 2 * y 2 * y 3 + (-9 : R) * a * b ^(6:ℕ) * y 1 * y 4 * y 4 + (-42 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 4 * y 4 + (-58 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 4 * y 4 + (-44 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 4 * y 4 + (-14 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 4 * y 4 + (-2 : R) * a ^(6:ℕ) * b * y 1 * y 4 * y 4 + (-6 : R) * a ^(7:ℕ) * y 1 * y 4 * y 4 + (6 : R) * b ^(7:ℕ) * y 1 * y 3 * y 3 + (24 : R) * a * b ^(6:ℕ) * y 1 * y 3 * y 3 + (6 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 3 * y 3 + (-30 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 3 * y 3 + (-10 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 3 * y 3 + (34 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 3 * y 3 + (30 : R) * a ^(6:ℕ) * b * y 1 * y 3 * y 3 + (8 : R) * a ^(7:ℕ) * y 1 * y 3 * y 3 + b ^(7:ℕ) * y 1 * y 2 * y 4 + (9 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 4 + (3 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 4 + (-38 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 4 + (-33 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 4 + (14 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 4 + (33 : R) * a ^(6:ℕ) * b * y 1 * y 2 * y 4 + (15 : R) * a ^(7:ℕ) * y 1 * y 2 * y 4 + b ^(7:ℕ) * y 1 * y 2 * y 2 + (4 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 2 + (8 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 2 + (2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 2 + (-14 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 2 + -a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 2 + (17 : R) * a ^(6:ℕ) * b * y 1 * y 2 * y 2 + (10 : R) * a ^(7:ℕ) * y 1 * y 2 * y 2 + (4 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 3 + (7 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 3 + (-6 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 3 + (-8 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 3 + (7 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 3 + (12 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 3 + (3 : R) * a ^(7:ℕ) * y 1 * y 1 * y 3 + -b ^(7:ℕ) * y 0 * y 3 * y 4 + a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 3 * y 4 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 3 * y 4 + (-2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 3 * y 4

private def rR3 {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  (-10 : R) * a * b ^(6:ℕ) * y 4 * y 4 * y 4 + (-43 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 4 * y 4 * y 4 + (-77 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 4 * y 4 * y 4 + (-86 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 4 * y 4 * y 4 + (-47 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 4 * y 4 * y 4 + (9 : R) * a ^(6:ℕ) * b * y 4 * y 4 * y 4 + (14 : R) * a ^(7:ℕ) * y 4 * y 4 * y 4 + (9 : R) * b ^(7:ℕ) * g * y 3 * y 4 * y 4 + (21 : R) * a * b ^(6:ℕ) * g * y 3 * y 4 * y 4 + (5 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 3 * y 4 * y 4 + (-27 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 4 * y 4 + -a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 4 * y 4 + (27 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 4 * y 4 + (22 : R) * a ^(6:ℕ) * b * g * y 3 * y 4 * y 4 + (7 : R) * a ^(7:ℕ) * g * y 3 * y 4 * y 4 + (15 : R) * b ^(7:ℕ) * y 3 * y 3 * y 4 + (32 : R) * a * b ^(6:ℕ) * y 3 * y 3 * y 4 + (-45 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 3 * y 4 + a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 3 * y 4 + (57 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 3 * y 4 + (44 : R) * a ^(6:ℕ) * b * y 3 * y 3 * y 4 + (11 : R) * a ^(7:ℕ) * y 3 * y 3 * y 4 + (3 : R) * a * b ^(6:ℕ) * y 2 * y 4 * y 4 + (15 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 4 * y 4 + (37 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 4 * y 4 + (27 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 4 * y 4 + (-18 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 4 * y 4 + (-15 : R) * a ^(6:ℕ) * b * y 2 * y 4 * y 4 + (3 : R) * a ^(7:ℕ) * y 2 * y 4 * y 4 + (-3 : R) * b ^(7:ℕ) * y 2 * y 3 * y 3 + (-12 : R) * a * b ^(6:ℕ) * y 2 * y 3 * y 3 + (-26 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 3 * y 3 + (-9 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 3 * y 3 + (11 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 3 * y 3 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 3 * y 3 + (-2 : R) * a ^(6:ℕ) * b * y 2 * y 3 * y 3 + -a ^(7:ℕ) * y 2 * y 3 * y 3 + (-2 : R) * b ^(7:ℕ) * y 2 * y 2 * y 4 + (-10 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 4 + (-26 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 4 + (-14 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 4 + (43 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 4 + (40 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 4 + (-13 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 4 + (-12 : R) * a ^(7:ℕ) * y 2 * y 2 * y 4 + -b ^(7:ℕ) * y 2 * y 2 * y 2 + -a * b ^(6:ℕ) * y 2 * y 2 * y 2 + (-10 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 2 + (-15 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 2 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 2 + (14 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 2 + (6 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 2 + (-5 : R) * a ^(7:ℕ) * y 2 * y 2 * y 2 + (-3 : R) * b ^(7:ℕ) * g * y 1 * y 4 * y 4 + (6 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 1 * y 4 * y 4 + (-6 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 1 * y 4 * y 4 + (-3 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 1 * y 4 * y 4 + (3 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 1 * y 4 * y 4 + (11 : R) * b ^(7:ℕ) * y 1 * y 3 * y 4 + (42 : R) * a * b ^(6:ℕ) * y 1 * y 3 * y 4 + (37 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 3 * y 4 + (-36 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 3 * y 4 + (-32 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 3 * y 4 + (57 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 3 * y 4 + (76 : R) * a ^(6:ℕ) * b * y 1 * y 3 * y 4 + (25 : R) * a ^(7:ℕ) * y 1 * y 3 * y 4 + -b ^(7:ℕ) * y 1 * y 2 * y 3 + (-2 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 3 + (-9 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 3 + (-12 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 3 + (6 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 3 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 3 + (-3 : R) * a ^(7:ℕ) * y 1 * y 2 * y 3 + (2 : R) * b ^(7:ℕ) * y 1 * y 1 * y 4 + (8 : R) * a * b ^(6:ℕ) * y 1 * y 1 * y 4 + (15 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 4 + (-4 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 4 + (-21 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 4 + (5 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 4 + (27 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 4 + (15 : R) * a ^(7:ℕ) * y 1 * y 1 * y 4 + a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 2 + a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 2 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 2 + (-2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 1 * y 2 + a ^(7:ℕ) * y 1 * y 1 * y 2 + a * b ^(6:ℕ) * y 0 * y 4 * y 4 + -a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 4 * y 4 + (3 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 4 * y 4 + (2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 4 * y 4 + (-2 : R) * a ^(7:ℕ) * y 0 * y 4 * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 3 * y 3 + (2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 3 * y 3 + (2 : R) * a ^(6:ℕ) * b * y 0 * y 3 * y 3 + (2 : R) * a * b ^(6:ℕ) * y 0 * y 2 * y 4 + (-2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 2 * y 4 + (2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 2 * y 4 + (-2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 2 * y 4 + (-2 : R) * a ^(6:ℕ) * b * y 0 * y 2 * y 4 + b ^(7:ℕ) * y 0 * y 2 * y 2 + (-2 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 2 * y 2 + (2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 2 * y 2 + a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 2 * y 2 + -a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 2 * y 2 + -a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 0 * y 4 + -a ^(3:ℕ) * b ^(4:ℕ) * y 0 * y 0 * y 4 + (2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 0 * y 0 * y 4 + (2 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 0 * y 4 + -a ^(7:ℕ) * y 0 * y 0 * y 4

private def rR4 {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) : R :=
  (-6 : R) * b ^(7:ℕ) * g * y 4 * y 4 * y 4 + (-33 : R) * a * b ^(6:ℕ) * g * y 4 * y 4 * y 4 + (-66 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 4 * y 4 * y 4 + (-38 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 4 * y 4 * y 4 + (41 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 4 * y 4 * y 4 + (47 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 4 * y 4 * y 4 + (-2 : R) * a ^(6:ℕ) * b * g * y 4 * y 4 * y 4 + (-14 : R) * a ^(7:ℕ) * g * y 4 * y 4 * y 4 + (28 : R) * b ^(7:ℕ) * y 3 * y 4 * y 4 + (68 : R) * a * b ^(6:ℕ) * y 3 * y 4 * y 4 + (71 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 4 * y 4 + (72 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 4 * y 4 + (95 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 4 * y 4 + (47 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 4 * y 4 + (-17 : R) * a ^(6:ℕ) * b * y 3 * y 4 * y 4 + (-16 : R) * a ^(7:ℕ) * y 3 * y 4 * y 4 + (3 : R) * b ^(7:ℕ) * g * y 3 * y 3 * y 4 + (6 : R) * a * b ^(6:ℕ) * g * y 3 * y 3 * y 4 + (-6 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 3 * y 3 * y 4 + (-3 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 3 * y 3 * y 4 + (3 : R) * a ^(5:ℕ) * b ^(2:ℕ) * g * y 3 * y 3 * y 4 + (10 : R) * b ^(7:ℕ) * y 3 * y 3 * y 3 + (16 : R) * a * b ^(6:ℕ) * y 3 * y 3 * y 3 + (3 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 3 * y 3 * y 3 + (-3 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 3 * y 3 * y 3 + (7 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 3 * y 3 * y 3 + (10 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 3 * y 3 * y 3 + (5 : R) * a ^(6:ℕ) * b * y 3 * y 3 * y 3 + a ^(7:ℕ) * y 3 * y 3 * y 3 + (-3 : R) * a ^(2:ℕ) * b ^(5:ℕ) * g * y 2 * y 4 * y 4 + (-3 : R) * a ^(3:ℕ) * b ^(4:ℕ) * g * y 2 * y 4 * y 4 + (6 : R) * a ^(4:ℕ) * b ^(3:ℕ) * g * y 2 * y 4 * y 4 + (-6 : R) * a ^(6:ℕ) * b * g * y 2 * y 4 * y 4 + (3 : R) * a ^(7:ℕ) * g * y 2 * y 4 * y 4 + (3 : R) * b ^(7:ℕ) * y 2 * y 3 * y 4 + (7 : R) * a * b ^(6:ℕ) * y 2 * y 3 * y 4 + (-28 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 3 * y 4 + (-36 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 3 * y 4 + (30 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 3 * y 4 + (56 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 3 * y 4 + (6 : R) * a ^(6:ℕ) * b * y 2 * y 3 * y 4 + (-8 : R) * a ^(7:ℕ) * y 2 * y 3 * y 4 + (4 : R) * a * b ^(6:ℕ) * y 2 * y 2 * y 3 + (4 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 2 * y 2 * y 3 + (-6 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 2 * y 2 * y 3 + (-8 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 2 * y 2 * y 3 + (7 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 2 * y 2 * y 3 + (12 : R) * a ^(6:ℕ) * b * y 2 * y 2 * y 3 + (3 : R) * a ^(7:ℕ) * y 2 * y 2 * y 3 + (2 : R) * b ^(7:ℕ) * y 1 * y 4 * y 4 + (12 : R) * a * b ^(6:ℕ) * y 1 * y 4 * y 4 + (32 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 4 * y 4 + (48 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 4 * y 4 + (55 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 4 * y 4 + (29 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 4 * y 4 + (-21 : R) * a ^(6:ℕ) * b * y 1 * y 4 * y 4 + (-22 : R) * a ^(7:ℕ) * y 1 * y 4 * y 4 + (2 : R) * b ^(7:ℕ) * y 1 * y 3 * y 3 + (6 : R) * a * b ^(6:ℕ) * y 1 * y 3 * y 3 + (-7 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 3 * y 3 + -a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 3 * y 3 + (9 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 3 * y 3 + (5 : R) * a ^(6:ℕ) * b * y 1 * y 3 * y 3 + (2 : R) * a ^(7:ℕ) * y 1 * y 3 * y 3 + -b ^(7:ℕ) * y 1 * y 2 * y 4 + (-6 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 4 + (-17 : R) * a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 2 * y 4 + (-22 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 4 + (4 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 4 + (23 : R) * a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 4 + (4 : R) * a ^(6:ℕ) * b * y 1 * y 2 * y 4 + (-7 : R) * a ^(7:ℕ) * y 1 * y 2 * y 4 + -b ^(7:ℕ) * y 1 * y 2 * y 2 + (-2 : R) * a * b ^(6:ℕ) * y 1 * y 2 * y 2 + (2 : R) * a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 2 * y 2 + a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 2 * y 2 + -a ^(5:ℕ) * b ^(2:ℕ) * y 1 * y 2 * y 2 + a ^(2:ℕ) * b ^(5:ℕ) * y 1 * y 1 * y 3 + a ^(3:ℕ) * b ^(4:ℕ) * y 1 * y 1 * y 3 + (-2 : R) * a ^(4:ℕ) * b ^(3:ℕ) * y 1 * y 1 * y 3 + (2 : R) * a ^(6:ℕ) * b * y 1 * y 1 * y 3 + -a ^(7:ℕ) * y 1 * y 1 * y 3 + b ^(7:ℕ) * y 0 * y 3 * y 4 + a * b ^(6:ℕ) * y 0 * y 3 * y 4 + a ^(2:ℕ) * b ^(5:ℕ) * y 0 * y 3 * y 4 + -a ^(5:ℕ) * b ^(2:ℕ) * y 0 * y 3 * y 4

/-! ## The certificate -/

/-- **The certificate.**  In every commutative ring with `5 = 0`, component `k` of the inverse
quadro–cubic map evaluated on `phiAS · y` is an explicit combination of the five transported
Pfaffians at `3g`. -/
private lemma certR {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R) (y : Fin 5 → R)
    (k : Fin 5) :
    kleinRAS a b g (fun i => ∑ j, phiAS a b i j * y j) k
      = ∑ i : Fin 5, cofR a b g y k i * kleinPAS a b (3 * g) y i := by
  rw [← zR_eq a b y]
  fin_cases k
  · change kleinRAS a b g (zR a b y) (0 : Fin 5) = ∑ i : Fin 5, cofR a b g y (0 : Fin 5) i * kleinPAS a b (3 * g) y i
    have hkey : kleinRAS a b g (zR a b y) (0 : Fin 5) - (∑ i : Fin 5, cofR a b g y (0 : Fin 5) i * kleinPAS a b (3 * g) y i) = 5 * rR0 a b g y := by
        simp only [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
          kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
          cofR, zR, rR0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_five]
        refl_ring1
    rw [h5, zero_mul] at hkey
    exact sub_eq_zero.mp hkey
  · change kleinRAS a b g (zR a b y) (1 : Fin 5) = ∑ i : Fin 5, cofR a b g y (1 : Fin 5) i * kleinPAS a b (3 * g) y i
    have hkey : kleinRAS a b g (zR a b y) (1 : Fin 5) - (∑ i : Fin 5, cofR a b g y (1 : Fin 5) i * kleinPAS a b (3 * g) y i) = 5 * rR1 a b g y := by
        simp only [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
          kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
          cofR, zR, rR1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_five]
        refl_ring1
    rw [h5, zero_mul] at hkey
    exact sub_eq_zero.mp hkey
  · change kleinRAS a b g (zR a b y) (2 : Fin 5) = ∑ i : Fin 5, cofR a b g y (2 : Fin 5) i * kleinPAS a b (3 * g) y i
    have hkey : kleinRAS a b g (zR a b y) (2 : Fin 5) - (∑ i : Fin 5, cofR a b g y (2 : Fin 5) i * kleinPAS a b (3 * g) y i) = 5 * rR2 a b g y := by
        simp only [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
          kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
          cofR, zR, rR2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_five]
        refl_ring1
    rw [h5, zero_mul] at hkey
    exact sub_eq_zero.mp hkey
  · change kleinRAS a b g (zR a b y) (3 : Fin 5) = ∑ i : Fin 5, cofR a b g y (3 : Fin 5) i * kleinPAS a b (3 * g) y i
    have hkey : kleinRAS a b g (zR a b y) (3 : Fin 5) - (∑ i : Fin 5, cofR a b g y (3 : Fin 5) i * kleinPAS a b (3 * g) y i) = 5 * rR3 a b g y := by
        simp only [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
          kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
          cofR, zR, rR3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_five]
        refl_ring1
    rw [h5, zero_mul] at hkey
    exact sub_eq_zero.mp hkey
  · change kleinRAS a b g (zR a b y) (4 : Fin 5) = ∑ i : Fin 5, cofR a b g y (4 : Fin 5) i * kleinPAS a b (3 * g) y i
    have hkey : kleinRAS a b g (zR a b y) (4 : Fin 5) - (∑ i : Fin 5, cofR a b g y (4 : Fin 5) i * kleinPAS a b (3 * g) y i) = 5 * rR4 a b g y := by
        simp only [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
          kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
          cofR, zR, rR4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
          Fin.sum_univ_five]
        refl_ring1
    rw [h5, zero_mul] at hkey
    exact sub_eq_zero.mp hkey

/-! ## The target -/

theorem ASZPhiMemGen {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R) (y : Fin 5 → R)
    (k : Fin 5) :
    Work.MotAS.kleinRAS a b g (fun i => ∑ j, Work.MotAS.phiAS a b i j * y j) k
      ∈ Ideal.radical (Ideal.span (Set.range (fun i : Fin 5 => Work.MotAS.kleinPAS a b (3 * g) y i))) := by
  apply Ideal.le_radical
  rw [certR h5 a b g y k]
  exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

end Work.MotC5N3
