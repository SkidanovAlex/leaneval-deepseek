/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib

/-!
# Small real-power bookkeeping lemmas for the reduction of `AreaA2`

The statement `PeluseInverseKMT` uses real exponents (`C * δ⁻¹ ^ K` with `K : ℝ`), while all the
quantitative bounds inside this area use natural exponents.  This module collects the (elementary)
conversions.
-/

set_option autoImplicit false

namespace Work.Peluse

/-- A natural exponent, written as a real one. -/
lemma rpow_nat_eq_pow (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n

lemma rpow_inv_nat_eq_inv_pow (x : ℝ) (n : ℕ) : (x⁻¹) ^ (n : ℝ) = (x ^ n)⁻¹ := by
  rw [rpow_nat_eq_pow, inv_pow]

/-- For `0 < x ≤ 1`, the map `a ↦ x ^ a` is antitone. -/
lemma rpow_le_rpow_of_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {a b : ℝ} (hab : b ≤ a) :
    x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hab

lemma rpow_le_one' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {a : ℝ} (ha : 0 ≤ a) : x ^ a ≤ 1 :=
  Real.rpow_le_one hx0 hx1 ha

lemma one_le_rpow' {x : ℝ} (hx1 : 1 ≤ x) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ x ^ a :=
  Real.one_le_rpow hx1 ha

lemma rpow_mul_self (x : ℝ) (hx0 : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) :=
  (Real.rpow_add hx0 a b).symm

/-- Two bounds for `x ^ a` obtained by splitting off a natural power. -/
lemma rpow_le_of_pow_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {a : ℝ} {m n : ℕ} (hmn : n ≤ m) :
    x ^ (m : ℝ) ≤ x ^ (n : ℝ) :=
  rpow_le_rpow_of_le_one hx0 hx1 (by exact_mod_cast hmn)

end Work.Peluse
