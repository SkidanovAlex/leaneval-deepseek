/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence.ArtinSchreier
-/
import Mathlib
import Submission.Work.TorsorExistence.ArtinSchreier.Basic
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Artin–Schreier irreducibility, degree five

Over a field `𝕜` of characteristic `5`, `X ^ 5 - X - a` is irreducible as soon as `a` is not of
the form `b ^ 5 - b`.

The argument is the elementary one: by `Polynomial.irreducible_iff_lt_natDegree_lt` it suffices
to exclude monic divisors of degree `1` or `2`.
* A monic divisor of degree `1` is `X + C c`, and dividing forces `f (-c) = 0`.
* For a monic divisor `q = X ^ 2 + C c * X + C c₀` of degree `2` put `s := C (-c) - X`.  Then
  `q.comp s = q`, so `q` divides `f.comp s` as well as `f`; adding the two and using Frobenius
  in characteristic `5` gives the polynomial identity
  `f.comp s + f = C (c - c ^ 5 - 2 * a)`.  Hence `q` divides a constant polynomial, which is
  possible only if that constant is `0`: `c - c ^ 5 - 2 * a = 0`, and then `a = (2 * c) ^ 5 - 2 * c`.
-/

set_option autoImplicit false

universe u

open Polynomial

namespace Work.TorsorExistence.ArtinSchreier

/-- **Artin–Schreier irreducibility, degree five.**  Over a field `𝕜` of characteristic `5`,
`X ^ 5 - X - a` is irreducible as soon as `a` is not of the form `b ^ 5 - b`. -/
theorem irreducible_X_pow_five_sub_X_sub_C {𝕜 : Type u} [Field 𝕜] [CharP 𝕜 5] (a : 𝕜)
    (ha : ¬ ∃ b : 𝕜, b ^ 5 - b = a) : Irreducible (X ^ 5 - X - C a : 𝕜[X]) := by
  have hnat : (X ^ 5 - X - C a : 𝕜[X]).natDegree = 5 := by
    have h : (X ^ 5 - X - C a : 𝕜[X]) = (X ^ 5 - C a) - X := by ring
    rw [h, natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow_sub_C
    · rw [natDegree_X, natDegree_X_pow_sub_C]; norm_num
  have hf0 : (X ^ 5 - X - C a : 𝕜[X]) ≠ 0 := by
    intro h; rw [h] at hnat; simp at hnat
  have hfunit : ¬ IsUnit (X ^ 5 - X - C a : 𝕜[X]) := by
    intro h
    rw [isUnit_iff] at h
    obtain ⟨r, -, hrC⟩ := h
    have h0 : (X ^ 5 - X - C a : 𝕜[X]).natDegree = 0 := by rw [← hrC]; exact natDegree_C r
    omega
  rw [irreducible_iff_lt_natDegree_lt hf0 hfunit]
  intro q hqmonic hqmem hqdiv
  rw [hnat, Finset.mem_Ioc] at hqmem
  have hqdeg : q.natDegree = 1 ∨ q.natDegree = 2 := by omega
  rcases hqdeg with hq1 | hq2
  · -- a monic divisor of degree one has a root in `𝕜`
    obtain ⟨c, hc⟩ : ∃ c : 𝕜, q = X + C c := ⟨q.coeff 0, hqmonic.eq_X_add_C hq1⟩
    have hroot : (X - C (-c)) ∣ (X ^ 5 - X - C a : 𝕜[X]) := by
      rw [show (X - C (-c) : 𝕜[X]) = q from by rw [hc]; simp only [map_neg]; ring]
      exact hqdiv
    rw [dvd_iff_isRoot, IsRoot.def] at hroot
    simp only [eval_sub, eval_pow, eval_X, eval_C] at hroot
    exact ha ⟨-c, by linear_combination hroot⟩
  · -- a monic divisor of degree two
    obtain ⟨c, c0, hqexp⟩ : ∃ c c0 : 𝕜, q = X ^ 2 + C c * X + C c0 := by
      refine ⟨q.coeff 1, q.coeff 0, ?_⟩
      have hc2 : q.coeff 2 = 1 := by rw [← hq2]; exact hqmonic.coeff_natDegree
      conv_lhs => rw [as_sum_range_C_mul_X_pow q, hq2]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2, C_1, pow_zero, pow_one,
        pow_two, mul_one, zero_add]
      first | refl_ring1 | ring
    have hqcomp : q.comp (C (-c) - X) = q := by
      rw [hqexp]
      simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
      rw [show (C (-c) : 𝕜[X]) = -C c from by rw [map_neg]]
      first | refl_ring1 | ring
    have hcompf : (X ^ 5 - X - C a : 𝕜[X]).comp (C (-c) - X)
        + (X ^ 5 - X - C a : 𝕜[X]) = C (c - c ^ 5 - 2 * a) := by
      have h5 : (5 : 𝕜[X]) = 0 := CharP.cast_eq_zero 𝕜[X] 5
      have hpow : (C (-c) - X : 𝕜[X]) ^ 5 = (C (-c)) ^ 5 - X ^ 5 := sub_pow_five h5 _ _
      rw [sub_comp, sub_comp, pow_comp, X_comp, C_comp, hpow]
      rw [show (((C (-c) : 𝕜[X])) ^ 5) = C ((-c) ^ 5) from by rw [map_pow]]
      rw [show ((-c : 𝕜)) ^ 5 = -(c ^ 5) from by ring]
      ring_nf
      have h2 : (2 : 𝕜[X]) = C (2 : 𝕜) := by
        rw [C_eq_algebraMap]; exact (map_natCast _ 2).symm
      rw [mul_comm (C a) 2, h2, ← map_mul, ← map_sub, ← map_sub]
      congr 1
      first | refl_ring1 | ring
    have hdiv1 : q ∣ (X ^ 5 - X - C a : 𝕜[X]).comp (C (-c) - X) := by
      obtain ⟨r, hr⟩ := hqdiv
      exact ⟨r.comp (C (-c) - X), by rw [hr, mul_comp, hqcomp]⟩
    have hdiv2 : q ∣ C (c - c ^ 5 - 2 * a) := by
      rw [← hcompf]
      exact dvd_add hdiv1 hqdiv
    have hy : c - c ^ 5 - 2 * a = 0 := by
      by_contra hne
      have hne' : (C (c - c ^ 5 - 2 * a) : 𝕜[X]) ≠ 0 := by
        rw [Ne, C_eq_zero]; exact hne
      have hle := natDegree_le_of_dvd hdiv2 hne'
      rw [hq2, natDegree_C] at hle
      omega
    have h5 : (5 : 𝕜) = 0 := CharP.cast_eq_zero 𝕜 5
    have h2c : (2 * c) ^ 5 = 2 * c ^ 5 := by
      linear_combination (norm := first | refl_ring1 | ring1) (6 * c ^ 5) * h5
    exact ha ⟨2 * c, by rw [h2c]; linear_combination (-2) * hy - a * h5⟩

end Work.TorsorExistence.ArtinSchreier
