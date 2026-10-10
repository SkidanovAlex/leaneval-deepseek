/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Klein--Fisher identities (audit node **K1**)

Polynomial identities with integer coefficients in the parameters `a b` and the coordinates,
stated for a general commutative ring `R`; they therefore hold in every commutative ring and
specialise by instantiating `R` (to `𝕜`, to `𝕜[y]`, to `L ⊗ 𝕜[y]`, after substituting the
twisted/Galois coordinates, …).

* `kleinP_shift`, `kleinQ_shift`, `kleinR_shift`, `kleinSec_shift`, `kleinSecDual_shift`: the
  cyclic shift `x_i ↦ x_{i+1}` permutes the Pfaffians by `k ↦ k+3` (and the `R_k` by `k ↦ k+2`)
  and fixes `q`, `s`, `s'`.
* `kleinM_mul_kleinP` — `M · p = 0`: the `p_k` are the Pfaffians of `M`.
* **I1** `kleinR_kleinP`: `R_i(p(x)) = s(x) x_i` (inverse quadro-cubic relation).
* **I2** `kleinP_kleinR`: `p_i(R(z)) = s'(z) z_i`.
* **I3** `kleinSecDual_kleinP`: `s'(p(x)) = s(x)^2`.
* `kleinQ_stereo`: `q(y(v)) = q(v)^2 q(p)` for stereographic `y(v) = q(v)p - b(p,v)v`.
* `kleinBilin_stereo`: `b(p, y(v)) = 2 q(v) q(p) - b(p,v)^2`.

(The remaining identity I4, `s(R(z)) = s'(z)^3`, is *not* proved by `ring` here: the composed
degree-15 expression is far too large.  See `KleinIdents`-guide below / the module
`Submission.Work.MotK.KleinI4`.)

Proof recipe of this file: `simp only [<component definitions>, <coordinate definitions>]`
then `ring`.  Componentwise lemmas use numeric indices so that `ring` sees the same atoms;
the bundled `∀ i` versions are obtained by `fin_cases i` and `change` to the numeric form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-! ## Shift equivariance -/

theorem kleinP_shift_zero (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) 0 = kleinP a b x 3 := by
  simp only [kleinP_zero, kleinP_three, kleinP0, kleinP3, kleinShift_zero, kleinShift_one,
    kleinShift_two, kleinShift_three, kleinShift_four] <;> ring_nf

theorem kleinP_shift_one (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) 1 = kleinP a b x 4 := by
  simp only [kleinP_one, kleinP_four, kleinP1, kleinP4, kleinShift_zero, kleinShift_one,
    kleinShift_two, kleinShift_three, kleinShift_four] <;> ring_nf

theorem kleinP_shift_two (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) 2 = kleinP a b x 0 := by
  simp only [kleinP_two, kleinP_zero, kleinP2, kleinP0, kleinShift_zero, kleinShift_one,
    kleinShift_two, kleinShift_three, kleinShift_four] <;> ring_nf

theorem kleinP_shift_three (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) 3 = kleinP a b x 1 := by
  simp only [kleinP_three, kleinP_one, kleinP3, kleinP1, kleinShift_zero, kleinShift_one,
    kleinShift_two, kleinShift_three, kleinShift_four] <;> ring_nf

theorem kleinP_shift_four (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) 4 = kleinP a b x 2 := by
  simp only [kleinP_four, kleinP_two, kleinP4, kleinP2, kleinShift_zero, kleinShift_one,
    kleinShift_two, kleinShift_three, kleinShift_four] <;> ring_nf

theorem kleinP_shift (a b : R) (x : Fin 5 → R) :
    kleinP a b (kleinShift x) = kleinShift (kleinShift (kleinShift (kleinP a b x))) := by
  funext k
  fin_cases k <;>
    simp only [kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three, kleinShift_four, kleinShift_zero', kleinShift_one', kleinShift_two', kleinShift_three', kleinShift_four', Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;>
    refl_ring1

theorem kleinQ_shift (a b : R) (x : Fin 5 → R) : kleinQ a b (kleinShift x) = kleinQ a b x := by
  simp only [kleinQ, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three,
    kleinShift_four]
  refl_ring1

theorem kleinR_shift (a b : R) (z : Fin 5 → R) :
    kleinR a b (kleinShift z) = kleinShift (kleinShift (kleinR a b z)) := by
  funext k
  fin_cases k <;>
    simp only [kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three, kleinShift_four, kleinShift_zero', kleinShift_one', kleinShift_two', kleinShift_three', kleinShift_four', Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    refl_ring1

theorem kleinSec_shift (a b : R) (x : Fin 5 → R) : kleinSec a b (kleinShift x) = kleinSec a b x := by
  simp only [kleinSec, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three,
    kleinShift_four]
  refl_ring1

theorem kleinSecDual_shift (a b : R) (z : Fin 5 → R) :
    kleinSecDual a b (kleinShift z) = kleinSecDual a b z := by
  simp only [kleinSecDual, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three,
    kleinShift_four]
  refl_ring1

/-! ## `M · p = 0` -/

theorem kleinM_mul_kleinP_zero (a b : R) (x : Fin 5 → R) :
    ∑ j, kleinM a b x 0 j * kleinP a b x j = 0 := by
  simp only [kleinM_zero, kleinM0, kleinP, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  refl_ring1

theorem kleinM_mul_kleinP_one (a b : R) (x : Fin 5 → R) :
    ∑ j, kleinM a b x 1 j * kleinP a b x j = 0 := by
  simp only [kleinM_one, kleinM1, kleinP, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  refl_ring1

theorem kleinM_mul_kleinP_two (a b : R) (x : Fin 5 → R) :
    ∑ j, kleinM a b x 2 j * kleinP a b x j = 0 := by
  simp only [kleinM_two, kleinM2, kleinP, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  refl_ring1

theorem kleinM_mul_kleinP_three (a b : R) (x : Fin 5 → R) :
    ∑ j, kleinM a b x 3 j * kleinP a b x j = 0 := by
  simp only [kleinM_three, kleinM3, kleinP, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  refl_ring1

theorem kleinM_mul_kleinP_four (a b : R) (x : Fin 5 → R) :
    ∑ j, kleinM a b x 4 j * kleinP a b x j = 0 := by
  simp only [kleinM_four, kleinM4, kleinP, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ']
  refl_ring1

theorem kleinM_mul_kleinP (a b : R) (x : Fin 5 → R) (i : Fin 5) :
    ∑ j, kleinM a b x i j * kleinP a b x j = 0 := by
  fin_cases i
  · change ∑ j, kleinM a b x 0 j * kleinP a b x j = 0
    exact kleinM_mul_kleinP_zero a b x
  · change ∑ j, kleinM a b x 1 j * kleinP a b x j = 0
    exact kleinM_mul_kleinP_one a b x
  · change ∑ j, kleinM a b x 2 j * kleinP a b x j = 0
    exact kleinM_mul_kleinP_two a b x
  · change ∑ j, kleinM a b x 3 j * kleinP a b x j = 0
    exact kleinM_mul_kleinP_three a b x
  · change ∑ j, kleinM a b x 4 j * kleinP a b x j = 0
    exact kleinM_mul_kleinP_four a b x

/-! ## I1: `R_i(p(x)) = s(x) x_i` -/

theorem kleinR_kleinP_zero (a b : R) (x : Fin 5 → R) :
    kleinR a b (kleinP a b x) 0 = kleinSec a b x * x 0 := by
  simp only [kleinR_zero, kleinR0, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinSec]
  refl_ring1

theorem kleinR_kleinP_one (a b : R) (x : Fin 5 → R) :
    kleinR a b (kleinP a b x) 1 = kleinSec a b x * x 1 := by
  simp only [kleinR_one, kleinR1, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinSec]
  refl_ring1

theorem kleinR_kleinP_two (a b : R) (x : Fin 5 → R) :
    kleinR a b (kleinP a b x) 2 = kleinSec a b x * x 2 := by
  simp only [kleinR_two, kleinR2, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinSec]
  refl_ring1

theorem kleinR_kleinP_three (a b : R) (x : Fin 5 → R) :
    kleinR a b (kleinP a b x) 3 = kleinSec a b x * x 3 := by
  simp only [kleinR_three, kleinR3, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinSec]
  refl_ring1

theorem kleinR_kleinP_four (a b : R) (x : Fin 5 → R) :
    kleinR a b (kleinP a b x) 4 = kleinSec a b x * x 4 := by
  simp only [kleinR_four, kleinR4, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinSec]
  refl_ring1

theorem kleinR_kleinP (a b : R) (x : Fin 5 → R) (i : Fin 5) :
    kleinR a b (kleinP a b x) i = kleinSec a b x * x i := by
  fin_cases i
  · change kleinR a b (kleinP a b x) 0 = kleinSec a b x * x 0
    exact kleinR_kleinP_zero a b x
  · change kleinR a b (kleinP a b x) 1 = kleinSec a b x * x 1
    exact kleinR_kleinP_one a b x
  · change kleinR a b (kleinP a b x) 2 = kleinSec a b x * x 2
    exact kleinR_kleinP_two a b x
  · change kleinR a b (kleinP a b x) 3 = kleinSec a b x * x 3
    exact kleinR_kleinP_three a b x
  · change kleinR a b (kleinP a b x) 4 = kleinSec a b x * x 4
    exact kleinR_kleinP_four a b x

/-! ## I2: `p_i(R(z)) = s'(z) z_i` -/

theorem kleinP_kleinR_zero (a b : R) (z : Fin 5 → R) :
    kleinP a b (kleinR a b z) 0 = kleinSecDual a b z * z 0 := by
  simp only [kleinP_zero, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinSecDual]
  refl_ring1

theorem kleinP_kleinR_one (a b : R) (z : Fin 5 → R) :
    kleinP a b (kleinR a b z) 1 = kleinSecDual a b z * z 1 := by
  simp only [kleinP_one, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinSecDual]
  refl_ring1

theorem kleinP_kleinR_two (a b : R) (z : Fin 5 → R) :
    kleinP a b (kleinR a b z) 2 = kleinSecDual a b z * z 2 := by
  simp only [kleinP_two, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinSecDual]
  refl_ring1

theorem kleinP_kleinR_three (a b : R) (z : Fin 5 → R) :
    kleinP a b (kleinR a b z) 3 = kleinSecDual a b z * z 3 := by
  simp only [kleinP_three, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinSecDual]
  refl_ring1

theorem kleinP_kleinR_four (a b : R) (z : Fin 5 → R) :
    kleinP a b (kleinR a b z) 4 = kleinSecDual a b z * z 4 := by
  simp only [kleinP_four, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinSecDual]
  refl_ring1

theorem kleinP_kleinR (a b : R) (z : Fin 5 → R) (i : Fin 5) :
    kleinP a b (kleinR a b z) i = kleinSecDual a b z * z i := by
  fin_cases i
  · change kleinP a b (kleinR a b z) 0 = kleinSecDual a b z * z 0
    exact kleinP_kleinR_zero a b z
  · change kleinP a b (kleinR a b z) 1 = kleinSecDual a b z * z 1
    exact kleinP_kleinR_one a b z
  · change kleinP a b (kleinR a b z) 2 = kleinSecDual a b z * z 2
    exact kleinP_kleinR_two a b z
  · change kleinP a b (kleinR a b z) 3 = kleinSecDual a b z * z 3
    exact kleinP_kleinR_three a b z
  · change kleinP a b (kleinR a b z) 4 = kleinSecDual a b z * z 4
    exact kleinP_kleinR_four a b z

/-! ## I3: `s'(p(x)) = s(x)^2` -/

theorem kleinSecDual_kleinP (a b : R) (x : Fin 5 → R) :
    kleinSecDual a b (kleinP a b x) = kleinSec a b x ^ 2 := by
  simp only [kleinSecDual, kleinSec, kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  refl_ring1

/-! ## The stereographic identities -/

theorem kleinQ_stereo (a b : R) (p v : Fin 5 → R) :
    kleinQ a b (kleinStereo a b p v) = kleinQ a b v ^ 2 * kleinQ a b p := by
  simp only [kleinQ, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinStereo, kleinBilin, Pi.add_apply]
  refl_ring1

theorem kleinBilin_stereo (a b : R) (p v : Fin 5 → R) :
    kleinBilin a b p (kleinStereo a b p v)
      = 2 * kleinQ a b v * kleinQ a b p - kleinBilin a b p v ^ 2 := by
  simp only [kleinQ, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinStereo, kleinBilin, Pi.add_apply]
  refl_ring1

/-! ## Homogeneity and I4 in multiplied form

`R` is homogeneous of degree 3 and `p`, `s`, `s'` of degrees 2, 5, 5 in the coordinates.  From
these and I1 + I2 one gets, in *every* commutative ring,

  `R_0(z) · s(R(z)) = R_0(z) · s'(z)^3`   (`kleinI4_mul`),

and, over a domain with `R_0(z) ≠ 0`, the genuine I4 `s(R(z)) = s'(z)^3`.
-/


theorem kleinP_homog (a b : R) (lam : R) (z : Fin 5 → R) :
    kleinP a b (fun i => lam * z i) = fun k => lam ^ 2 * kleinP a b z k := by
  funext k
  fin_cases k <;>
    simp only [kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four, kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four', kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three, kleinShift_four, kleinShift_zero', kleinShift_one', kleinShift_two', kleinShift_three', kleinShift_four', Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;>
    ring_nf

theorem kleinR_homog (a b : R) (lam : R) (z : Fin 5 → R) :
    kleinR a b (fun i => lam * z i) = fun k => lam ^ 3 * kleinR a b z k := by
  funext k
  fin_cases k <;>
    simp only [kleinR_zero, kleinR_one, kleinR_two, kleinR_three, kleinR_four, kleinR_zero', kleinR_one', kleinR_two', kleinR_three', kleinR_four', kleinR0, kleinR1, kleinR2, kleinR3, kleinR4, kleinShift_zero, kleinShift_one, kleinShift_two, kleinShift_three, kleinShift_four, kleinShift_zero', kleinShift_one', kleinShift_two', kleinShift_three', kleinShift_four', Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;>
    ring_nf

theorem kleinSec_homog (a b : R) (lam : R) (z : Fin 5 → R) :
    kleinSec a b (fun i => lam * z i) = lam ^ 5 * kleinSec a b z := by
  simp only [kleinSec]
  refl_ring1

theorem kleinSecDual_homog (a b : R) (lam : R) (z : Fin 5 → R) :
    kleinSecDual a b (fun i => lam * z i) = lam ^ 5 * kleinSecDual a b z := by
  simp only [kleinSecDual]
  refl_ring1

theorem kleinI4_mul (a b : R) (z : Fin 5 → R) :
    kleinR a b z 0 * kleinSec a b (kleinR a b z)
      = kleinR a b z 0 * kleinSecDual a b z ^ 3 := by
  have h1 : kleinR a b (kleinP a b (kleinR a b z))
      = fun i => kleinSec a b (kleinR a b z) * kleinR a b z i := by
    funext i
    exact kleinR_kleinP a b (kleinR a b z) i
  have h2 : kleinP a b (kleinR a b z) = fun i => kleinSecDual a b z * z i := by
    funext i
    exact kleinP_kleinR a b z i
  rw [h2, kleinR_homog] at h1
  have h0 := congrFun h1 0
  rw [mul_comm (kleinSecDual a b z ^ 3), mul_comm (kleinSec a b (kleinR a b z))] at h0
  exact h0.symm

theorem kleinSec_kleinR (a b : R) [IsDomain R] (z : Fin 5 → R) (hz : kleinR a b z 0 ≠ 0) :
    kleinSec a b (kleinR a b z) = kleinSecDual a b z ^ 3 :=
  mul_left_cancel₀ hz (kleinI4_mul a b z)

end Work.MotK
