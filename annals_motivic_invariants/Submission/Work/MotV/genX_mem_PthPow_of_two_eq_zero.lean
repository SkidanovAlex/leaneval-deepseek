/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# The coordinate `x` is a square in characteristic two when `a₁ = a₃ = 0`

Let `E` be a Weierstrass curve over a field `N` of characteristic `p` with `2 = 0` (so `p = 2`)
and `a₁ = a₃ = 0`; the Weierstrass equation of `E` is then `y² = x³ + a₂x² + a₄x + a₆`.
Since `N` is algebraically closed, the constants `a₂, a₄, a₆` have square roots `c₂, c₄, c₆`
in `N`, and the relation `y² = x³ + a₂x² + a₄x + a₆` can be solved for `x`: because in
characteristic two `(u + v + w)² = u² + v² + w²`, we get

  `(y + c₂x + c₆)² = y² + a₂x² + a₆ = x³ + a₄x = x (x + c₄)²`,

so that `x = ((y + c₂x + c₆)/(x + c₄))²` provided `x + c₄ ≠ 0` (which holds because `x` is
transcendental over `N`, so `x` is not a constant).

Hence `x = genX E` is a `p`-th power in the function field `N(E)`, i.e. it lies in
`Work.MotV.PthPow`.

## Main results

* `genX_eq_sq_of_relation_char_two`: the purely algebraic identity above;
* `genX_mem_PthPow_of_two_eq_zero`: `genX E ∈ PthPow (Func E) p`.
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

namespace Work.MotV

/-- **The algebraic core.**  In a field of characteristic two, if `y² = x³ + a₂x² + a₄x + a₆`
and the coefficients `a₂, a₄, a₆` are squares `c₂², c₄², c₆²`, then `x` is the square
`((y + c₂x + c₆)/(x + c₄))²`, provided `x + c₄ ≠ 0`. -/
theorem genX_eq_sq_of_relation_char_two {K : Type*} [Field K] (h2 : (2 : K) = 0)
    {x y c2 c4 c6 a2 a4 a6 : K} (hrel : y ^ 2 = x ^ 3 + a2 * x ^ 2 + a4 * x + a6)
    (hc2 : c2 ^ 2 = a2) (hc4 : c4 ^ 2 = a4) (hc6 : c6 ^ 2 = a6) (hx : x + c4 ≠ 0) :
    ((y + c2 * x + c6) / (x + c4)) ^ 2 = x := by
  have hsq : (y + c2 * x + c6) ^ 2 = x * (x + c4) ^ 2 := by
    linear_combination (norm := first | refl_ring1 | ring1) hrel + x ^ 2 * hc2 + hc6 - x * hc4 +
      (y * c2 * x + y * c6 + c2 * x * c6 - x ^ 2 * c4 + a2 * x ^ 2 + a6) * h2
  rw [div_pow, hsq, mul_div_cancel_right₀ _ (pow_ne_zero 2 hx)]

theorem genX_mem_PthPow_of_two_eq_zero {N : Type*} [Field N] [IsAlgClosed N]
    (E : WeierstrassCurve N) (p : ℕ) [Fact p.Prime] [CharP N p] (h2 : (2 : N) = 0)
    (h1 : E.a₁ = 0) (h3 : E.a₃ = 0) :
    Work.MotC2.genX E ∈ Work.MotV.PthPow (Work.MotC2.Func E) p := by
  -- `(2 : N) = 0` together with `Fact p.Prime` forces `p = 2`.
  have hp2 : p = 2 := by
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff N p 2).mp h2
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd
  -- square roots of the coefficients, in `N` (algebraically closed) and then in `N(E)`
  obtain ⟨u2, hu2⟩ := IsAlgClosed.exists_pow_nat_eq (k := N) E.a₂ (n := 2) (by norm_num)
  obtain ⟨u4, hu4⟩ := IsAlgClosed.exists_pow_nat_eq (k := N) E.a₄ (n := 2) (by norm_num)
  obtain ⟨u6, hu6⟩ := IsAlgClosed.exists_pow_nat_eq (k := N) E.a₆ (n := 2) (by norm_num)
  have hc2 : (algebraMap N (Work.MotC2.Func E) u2) ^ 2 =
      algebraMap N (Work.MotC2.Func E) E.a₂ := by rw [← map_pow, hu2]
  have hc4 : (algebraMap N (Work.MotC2.Func E) u4) ^ 2 =
      algebraMap N (Work.MotC2.Func E) E.a₄ := by rw [← map_pow, hu4]
  have hc6 : (algebraMap N (Work.MotC2.Func E) u6) ^ 2 =
      algebraMap N (Work.MotC2.Func E) E.a₆ := by rw [← map_pow, hu6]
  -- the Weierstrass relation in the function field, simplified with `a₁ = a₃ = 0`
  have hrel : (Work.MotC2.genY E) ^ 2 = (Work.MotC2.genX E) ^ 3 +
      algebraMap N (Work.MotC2.Func E) E.a₂ * (Work.MotC2.genX E) ^ 2 +
      algebraMap N (Work.MotC2.Func E) E.a₄ * Work.MotC2.genX E +
      algebraMap N (Work.MotC2.Func E) E.a₆ := by
    have h := Work.MotC2.genY_sq_relation E
    rw [h1, h3] at h
    simpa using h
  -- the field of fractions has characteristic two
  have h2K : (2 : Work.MotC2.Func E) = 0 := by
    rw [← map_ofNat (algebraMap N (Work.MotC2.Func E)) 2, h2, map_zero]
  -- `x + c₄ ≠ 0`, since otherwise `x` would be a constant
  have hxne : Work.MotC2.genX E + algebraMap N (Work.MotC2.Func E) u4 ≠ 0 := by
    intro hh
    refine Work.MotC2.genX_ne_algebraMap E (-u4) ?_
    rw [map_neg]
    linear_combination (norm := first | refl_ring1 | ring1) hh
  refine Work.MotV.mem_PthPow.mpr ⟨(Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) u2 * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) u6) /
      (Work.MotC2.genX E + algebraMap N (Work.MotC2.Func E) u4), ?_⟩
  rw [hp2]
  exact genX_eq_sq_of_relation_char_two h2K hrel hc2 hc4 hc6 hxne

end Work.MotV
