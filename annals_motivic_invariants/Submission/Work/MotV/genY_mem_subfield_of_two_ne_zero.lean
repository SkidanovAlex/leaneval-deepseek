/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The `y`-coordinate lies in any subfield containing the `p`-th powers and `x`

Let `K = N(E)` be the function field of a Weierstrass curve over an algebraically closed field
`N` of characteristic `p = char N ≠ 2`, and let `S ⊆ K` be a subfield containing every `p`-th
power and the coordinate `x = genX E`.  Then `y = genY E ∈ S`.

The proof is "complete the square": with `h = a₁x + a₃` and `g = x³ + a₂x² + a₄x + a₆` the
Weierstrass relation reads `y² + h y = g`.  Put `Z = 2y + h`; then `Z² = 4g + h² =: G`, and both
`h` and `G` lie in `S` (they are polynomials in `x` with constant coefficients, and every
constant is a `p`-th power).  Since `p` is odd, `Z^p = Z * (Z²)^k = Z * G^k` where `p = 2k + 1`;
as `Z^p ∈ S` (it is a `p`-th power) we get `Z ∈ S` (`G = 0` gives `Z = 0`, otherwise divide by
`G^k`), and finally `y = (Z - h)/2 ∈ S`.

This is the characteristic `≠ 2` counterpart of `genY_mem_subfield_of_two_eq_zero`.
-/

import Mathlib
import Submission.Work.MotV.PthPowDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV

theorem genY_mem_subfield_of_two_ne_zero {N : Type*} [Field N] [IsAlgClosed N]
    (E : WeierstrassCurve N) (p : ℕ) [Fact p.Prime] [CharP N p] (h2 : (2 : N) ≠ 0)
    (S : Subfield (Work.MotC2.Func E))
    (hKp : ∀ z ∈ Work.MotV.PthPow (Work.MotC2.Func E) p, z ∈ S)
    (hx : Work.MotC2.genX E ∈ S) : Work.MotC2.genY E ∈ S := by
  -- every constant is a `p`-th power, hence lies in `S`
  have hconst : ∀ c : N, algebraMap N (MotC2.Func E) c ∈ S :=
    fun c => hKp _ (algebraMap_mem_PthPow p E c)
  -- `p ≠ 2`, since `2 ≠ 0` in `N` and `N` has characteristic `p`
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (CharP.cast_eq_zero N 2)
  -- every polynomial in `x` with constant coefficients lies in `S`
  have hpoly : ∀ P : Polynomial N, Polynomial.aeval (MotC2.genX E) P ∈ S := by
    intro P
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    refine S.sum_mem (fun i _ => ?_)
    exact S.mul_mem (hconst _) (S.pow_mem hx i)
  set h := Polynomial.aeval (MotC2.genX E)
    (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) with hhdef
  set g := Polynomial.aeval (MotC2.genX E)
      (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄ * Polynomial.X
        + Polynomial.C E.a₆) with hgdef
  have hh : h ∈ S := by rw [hhdef]; exact hpoly _
  have hg : g ∈ S := by rw [hgdef]; exact hpoly _
  have hhval : h = algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
      algebraMap N (MotC2.Func E) E.a₃ := by
    rw [hhdef]; simp [Polynomial.aeval_def]
  have hgval : g = MotC2.genX E ^ 3 + algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E ^ 2
      + algebraMap N (MotC2.Func E) E.a₄ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₆ := by
    rw [hgdef]; simp [Polynomial.aeval_def]
  -- the Weierstrass relation, in the form `y² + h y = g`
  have hrel : MotC2.genY E ^ 2 + h * MotC2.genY E = g := by
    rw [hhval, hgval]
    have hs := MotC2.genY_sq_relation E
    linear_combination (norm := first | refl_ring1 | ring1) hs
  set Z := 2 * MotC2.genY E + h with hZdef
  set G := 4 * g + h ^ 2 with hGdef
  have h4S : (4 : MotC2.Func E) ∈ S := by
    rw [← map_ofNat (algebraMap N (MotC2.Func E)) 4]
    exact hconst 4
  have hG : G ∈ S := by
    rw [hGdef]
    exact S.add_mem (S.mul_mem h4S hg) (S.pow_mem hh 2)
  -- completing the square: `Z² = G`
  have hZ2 : Z ^ 2 = G := by
    rw [hZdef, hGdef]
    have key : (2 * MotC2.genY E + h) ^ 2 =
        4 * (MotC2.genY E ^ 2 + h * MotC2.genY E) + h ^ 2 := by ring
    rw [key, hrel]
  -- `p = 2k + 1`, so `Z^p = Z * G^k`
  obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime p) hp2
  have hZpS : Z ^ p ∈ S := hKp _ (mem_PthPow.mpr ⟨Z, rfl⟩)
  have hZp : Z ^ p = Z * G ^ k := by
    rw [hk, pow_succ, pow_mul, hZ2, mul_comm]
  have h2K : (2 : MotC2.Func E) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (MotC2.Func E) p 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hp2 h1
  have h2S : (2 : MotC2.Func E) ∈ S := by
    rw [← map_ofNat (algebraMap N (MotC2.Func E)) 2]
    exact hconst 2
  -- hence `Z ∈ S`
  have hZS : Z ∈ S := by
    by_cases hG0 : G = 0
    · have hZ0 : Z = 0 := by
        have hsq : Z * Z = 0 := by rw [← pow_two, hZ2, hG0]
        exact mul_self_eq_zero.mp hsq
      rw [hZ0]; exact S.zero_mem
    · have hGk : G ^ k ∈ S := S.pow_mem hG k
      have hGk0 : G ^ k ≠ 0 := pow_ne_zero k hG0
      have hmul : Z * G ^ k ∈ S := by rw [← hZp]; exact hZpS
      rw [← mul_inv_cancel_right₀ hGk0 Z]
      exact S.mul_mem hmul (S.inv_mem hGk)
  -- and finally `y = (Z - h)/2 ∈ S`
  have hy : MotC2.genY E = (Z - h) / 2 := by
    rw [eq_div_iff h2K, hZdef]
    first | refl_ring1 | ring
  rw [hy]
  exact S.div_mem (S.sub_mem hZS hh) h2S

end Work.MotV
