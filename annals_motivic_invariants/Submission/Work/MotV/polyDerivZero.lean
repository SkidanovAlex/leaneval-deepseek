/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Polynomials with vanishing Wronskian are proportional (char. 0)

If `p, q : N[X]` are polynomials over a field `N` of characteristic zero with vanishing Wronskian
`wronskian p q = p * q' - p' * q = 0` and `q ≠ 0`, then `p = C c * q` for a constant `c : N`:
the rational function `p / q` is a constant.  This is the algebraic form of "a function with zero
logarithmic derivative is constant".

Consequently, for any Weierstrass curve `E` over `N`, the value `xΦ E p / xΦ E q` of the
ratio in the function field `N(E)` is a constant.

## Main results

* `Work.MotV.exists_C_mul_of_wronskian_eq_zero`
* `Work.MotV.polyDerivZero`
-/

import Mathlib
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Polynomial

namespace Work.MotV

/-- **Polynomials with vanishing Wronskian are proportional.**  If `p' q = p q'` (equivalently
`wronskian p q = 0`) with `q ≠ 0` over a field of characteristic zero, then `p / q` is a constant,
i.e. `p = C c * q`.

The proof divides out the content of the pair: writing `p = d * p₁`, `q = d * q₁` with
`d = gcd p q`, the Wronskian identity becomes `d² * wronskian p₁ q₁ = 0`, so with `p₁`, `q₁`
coprime both derivatives vanish, and `p₁`, `q₁` are constants (characteristic zero). -/
lemma exists_C_mul_of_wronskian_eq_zero {N : Type*} [Field N] [CharZero N]
    (p q : Polynomial N) (hq : q ≠ 0) (h : Polynomial.wronskian p q = 0) :
    ∃ c : N, p = Polynomial.C c * q := by
  classical
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  obtain hgp : gcd p q ∣ p := gcd_dvd_left p q
  obtain hgq : gcd p q ∣ q := gcd_dvd_right p q
  have hd0 : gcd p q ≠ 0 := gcd_ne_zero_of_right hq
  have hp₁ : gcd p q * (p / gcd p q) = p := EuclideanDomain.mul_div_cancel' hd0 hgp
  have hq₁ : gcd p q * (q / gcd p q) = q := EuclideanDomain.mul_div_cancel' hd0 hgq
  have hcop : IsCoprime (p / gcd p q) (q / gcd p q) := isCoprime_div_gcd_div_gcd hq
  have hw2 : Polynomial.wronskian (p / gcd p q) (q / gcd p q) = 0 := by
    have hmain : Polynomial.wronskian (gcd p q * (p / gcd p q))
        (gcd p q * (q / gcd p q)) = 0 := by
      rw [hp₁, hq₁, h]
    rw [Polynomial.wronskian, Polynomial.derivative_mul, Polynomial.derivative_mul] at hmain
    have : Polynomial.wronskian (p / gcd p q) (q / gcd p q) * (gcd p q) ^ 2 = 0 := by
      rw [Polynomial.wronskian]
      linear_combination (norm := first | refl_ring1 | ring1) hmain
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' (pow_ne_zero 2 hd0)
  obtain ⟨hd1, hd2⟩ := hcop.wronskian_eq_zero_iff.mp hw2
  have e1 : p / gcd p q = Polynomial.C ((p / gcd p q).coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hd1
  have e2 : q / gcd p q = Polynomial.C ((q / gcd p q).coeff 0) :=
    Polynomial.eq_C_of_derivative_eq_zero hd2
  set a := (p / gcd p q).coeff 0
  set b := (q / gcd p q).coeff 0
  have hb : b ≠ 0 := by
    intro hb0
    have hz : q = 0 := by rw [← hq₁, e2, hb0, Polynomial.C_0, mul_zero]
    exact hq hz
  refine ⟨a * b⁻¹, ?_⟩
  have hac : Polynomial.C (a * b⁻¹) * (Polynomial.C b * gcd p q) = Polynomial.C a * gcd p q := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  calc p = gcd p q * (p / gcd p q) := hp₁.symm
    _ = gcd p q * Polynomial.C a := by rw [e1]
    _ = Polynomial.C a * gcd p q := mul_comm _ _
    _ = Polynomial.C (a * b⁻¹) * (Polynomial.C b * gcd p q) := hac.symm
    _ = Polynomial.C (a * b⁻¹) * (gcd p q * Polynomial.C b) := by rw [mul_comm (Polynomial.C b)]
    _ = Polynomial.C (a * b⁻¹) * (gcd p q * (q / gcd p q)) := by rw [e2]
    _ = Polynomial.C (a * b⁻¹) * q := by rw [hq₁]

theorem polyDerivZero (N : Type*) [Field N] [CharZero N] (E : WeierstrassCurve N)
    (p q : Polynomial N) (hq : q ≠ 0)
    (h : Polynomial.derivative p * q - p * Polynomial.derivative q = 0) :
    ∃ c : N, Work.MotC2.xPhi E p / Work.MotC2.xPhi E q =
      algebraMap N (Work.MotC2.Func E) c := by
  have hw : Polynomial.wronskian p q = 0 := by
    rw [Polynomial.wronskian]
    linear_combination (norm := first | refl_ring1 | ring1) -h
  obtain ⟨c, hc⟩ := exists_C_mul_of_wronskian_eq_zero p q hq hw
  by_cases hxq : Work.MotC2.xPhi E q = 0
  · exact ⟨0, by simp [hxq]⟩
  · refine ⟨c, ?_⟩
    have hC : Work.MotC2.xPhi E (Polynomial.C c) = algebraMap N (Work.MotC2.Func E) c := by
      simp [Work.MotC2.xPhi]
    have hkey : Work.MotC2.xPhi E p =
        algebraMap N (Work.MotC2.Func E) c * Work.MotC2.xPhi E q := by
      rw [hc, map_mul, hC]
    rw [hkey, mul_div_cancel_right₀ _ hxq]

end Work.MotV
