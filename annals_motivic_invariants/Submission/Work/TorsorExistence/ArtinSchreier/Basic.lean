/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence.ArtinSchreier
-/
import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Artin–Schreier theory in characteristic five: the roots of `X ^ 5 - X`

Let `R` be a commutative ring with `(5 : R) = 0` (in the applications `R` is a field of
characteristic `5`, or a polynomial ring over it).  Then

* `prod_range_five_sub_C`: `∏ i ∈ range 5, (T - C i) = T ^ 5 - T` for any `T : R[X]`,
* `prod_range_five_shift`: `∏ i ∈ range 5, (X - C (r + i)) = X ^ 5 - X - C (r ^ 5 - r)`,
* `pow_five_eq_self_exists`: in a field with `(5 : K) = 0` the solutions of `x ^ 5 = x`
  are exactly the "integers" `0, 1, 2, 3, 4`,
* `add_pow_five`, `sub_pow_five`: Frobenius, `(x ± y) ^ 5 = x ^ 5 ± y ^ 5`.

These are the algebraic core of Artin–Schreier theory for the prime `5`.
-/

set_option autoImplicit false

universe u

open Polynomial

namespace Work.TorsorExistence.ArtinSchreier

variable {R : Type u}

/-- In a commutative ring with `(5 : R) = 0`, the polynomial `T ^ 5 - T` factors as
`∏ i ∈ range 5, (T - C i)`; equivalently the roots of `℘` are the "integers" `0,…,4`. -/
theorem prod_range_five_sub_C [CommRing R] (h5 : (5 : R) = 0) (T : R[X]) :
    (∏ i ∈ Finset.range 5, (T - C (i : R))) = T ^ 5 - T := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  have hC : ∀ n : ℕ, (C (n : R) : R[X]) = (n : R[X]) := fun n => by
    rw [C_eq_algebraMap]; exact map_natCast _ n
  simp only [hC]
  ring_nf
  have h5X : (5 : R[X]) = 0 := by
    rw [← map_ofNat (algebraMap R R[X]) 5, h5, map_zero]
  linear_combination (norm := first | refl_ring1 | ring1) (5 * T - 10 * T ^ 2 + 7 * T ^ 3 - 2 * T ^ 4) * h5X

variable {S : Type u}

/-- Frobenius in characteristic `5`: `(x + y) ^ 5 = x ^ 5 + y ^ 5`. -/
theorem add_pow_five [CommRing S] (h5 : (5 : S) = 0) (x y : S) :
    (x + y) ^ 5 = x ^ 5 + y ^ 5 := by
  have h : (x + y) ^ 5 - (x ^ 5 + y ^ 5) =
      (5 : S) * (x ^ 4 * y + 2 * x ^ 3 * y ^ 2 + 2 * x ^ 2 * y ^ 3 + x * y ^ 4) := by
    first | refl_ring1 | ring
  rw [← sub_eq_zero, h, h5, zero_mul]

/-- Frobenius in characteristic `5`: `(x - y) ^ 5 = x ^ 5 - y ^ 5`. -/
theorem sub_pow_five [CommRing S] (h5 : (5 : S) = 0) (x y : S) :
    (x - y) ^ 5 = x ^ 5 - y ^ 5 := by
  have h : (x - y) ^ 5 - (x ^ 5 - y ^ 5) =
      (5 : S) * (-x ^ 4 * y + 2 * x ^ 3 * y ^ 2 - 2 * x ^ 2 * y ^ 3 + x * y ^ 4) := by
    first | refl_ring1 | ring
  rw [← sub_eq_zero, h, h5, zero_mul]

private theorem X_sub_C_pow_five [CommRing R] (h5 : (5 : R) = 0) (r : R) :
    (X - C r) ^ 5 = X ^ 5 - C (r ^ 5) := by
  have h5X : (5 : R[X]) = 0 := by
    rw [← map_ofNat (algebraMap R R[X]) 5, h5, map_zero]
  rw [← sub_eq_zero]
  rw [show (C (r ^ 5) : R[X]) = (C r) ^ 5 from by rw [map_pow]]
  have h : (X - C r) ^ 5 - (X ^ 5 - (C r) ^ 5) =
      (5 : R[X]) *
        (-X ^ 4 * C r + 2 * X ^ 3 * (C r) ^ 2 - 2 * X ^ 2 * (C r) ^ 3 + X * (C r) ^ 4) := by
    first | refl_ring1 | ring
  rw [h, h5X, zero_mul]

/-- Shifted form of `prod_range_five_sub_C`: the roots of `X ^ 5 - X - C (r ^ 5 - r)` are
`r, r + 1, …, r + 4`. -/
theorem prod_range_five_shift [CommRing R] (h5 : (5 : R) = 0) (r : R) :
    (∏ i ∈ Finset.range 5, ((X : R[X]) - C (r + i))) = X ^ 5 - X - C (r ^ 5 - r) := by
  have hpow : (X - C r) ^ 5 = X ^ 5 - C (r ^ 5) := X_sub_C_pow_five h5 r
  have h1 : (∏ i ∈ Finset.range 5, ((X - C r) - C (i : R))) = X ^ 5 - X - C (r ^ 5 - r) := by
    rw [prod_range_five_sub_C h5 (X - C r), hpow]
    rw [show (C (r ^ 5 - r) : R[X]) = C (r ^ 5) - C r from by rw [map_sub]]
    first | refl_ring1 | ring
  rw [← h1]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [map_add]; ring

/-- In a field with `(5 : K) = 0` the solutions of `x ^ 5 = x` are exactly `0, 1, 2, 3, 4`. -/
theorem pow_five_eq_self_exists {K : Type u} [Field K] (h5 : (5 : K) = 0) (x : K)
    (h : x ^ 5 = x) : ∃ i : ℕ, i < 5 ∧ x = (i : K) := by
  have key := congrArg (Polynomial.eval x) (prod_range_five_sub_C (R := K) h5 (X : K[X]))
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_C] at key
  have hx : x ^ 5 - x = 0 := by rw [h, sub_self]
  rw [hx] at key
  obtain ⟨i, hi, hz⟩ := Finset.prod_eq_zero_iff.mp key
  exact ⟨i, Finset.mem_range.mp hi, sub_eq_zero.mp hz⟩

end Work.TorsorExistence.ArtinSchreier
