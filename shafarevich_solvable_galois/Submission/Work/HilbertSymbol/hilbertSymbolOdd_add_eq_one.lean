/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `(a, b)_p = 1` at an odd prime when `a + b = 1`

The quadratic form `x² - a y² - b z²` has the nontrivial zero `(1,1,1)` as soon as `a + b = 1`,
so the quaternion algebra `(a, b)` splits at *every* place: `(a, 1 - a)_v = 1`.  This file proves
the corresponding statement for the explicit formula which *defines* `hilbertSymbolOdd` at an odd
prime `p` (the case `p = 2` is trivial from that same formula, the Legendre factors being trivial
in `(ZMod 2)ˣ`).

Write `α = v_p(a)`, `β = v_p(b)`.  Since `v_p(a+b) = v_p(1) = 0`:

* `α = β = 0`: the formula reads `(-1)⁰ (u_a/p)⁰ (u_b/p)⁰ = 1`;
* `α ≠ β`: then `min (α, β) = v_p(a + b) = 0`, so one of them, say `α`, is `0` while `β > 0`.
  Then `a = 1 - b ≡ 1 (mod p)`, hence `(u_a/p) = 1` and the formula reads `(u_a/p)^β = 1`;
* `α = β = t < 0`: then `u_a + u_b = p^{-t} ≡ 0 (mod p)`, so `u_b ≡ -u_a` and
  `(u_a/p)(u_b/p) = (-1/p)`.  Hence the formula becomes
  `(-1)^{t² c} ((-1/p))^t = (-1)^{t² c + t c} = (-1)^{c t (t+1)} = 1`, because `c = (p-1)/2` and
  `t (t+1)` is even.

The two non-formulaic inputs are isolated in the imported files
`legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos` (a `p`-adic unit congruent to `1` modulo
`p` has Legendre symbol `1`) and `legendreOf_mul_eq_legendreOf_neg_one_of_add_eq_one` (the value
`(u_a/p)(u_b/p) = (-1/p)` when `v_p(a) = v_p(b) < 0`).
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_eq_one_of_padicVal_eq_zero
import Submission.Work.HilbertSymbol.legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos
import Submission.Work.HilbertSymbol.legendreOf_mul_eq_legendreOf_neg_one_of_add_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-! ## The prime `2`: the formula is trivial

For `p = 2` the exponent `(p-1)/2` vanishes and `(ZMod 2)ˣ` is trivial, so both Legendre factors
of the explicit formula for `hilbertSymbolOdd 2` are `1`. -/

private theorem intUnitOf_negOnePow_nat (k : ℕ) : intUnitOf ((-1 : ℤ) ^ k) = (-1 : ℤˣ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpm : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
      rcases Nat.even_or_odd k with h | h
      · exact Or.inl h.neg_one_pow
      · exact Or.inr h.neg_one_pow
    rw [pow_succ, intUnitOf_mul hpm (Or.inr rfl), ih, pow_succ]
    simp

private theorem hilbertSymbolOdd_two_eq_one (a b : ℚˣ) : hilbertSymbolOdd 2 a b = 1 := by
  have hleg : ∀ x : ℚˣ, legendreOf 2 x = 1 := by
    intro x
    set w : (ZMod 2)ˣ := Units.map (PadicInt.toZMod (p := 2)) (unitPart 2 x) with hw
    have hne : (w : ZMod 2) ≠ 0 := w.ne_zero
    rw [legendreOf, legendreUnit, quadCharUnit, ← hw]
    rw [quadraticChar_eq_one_of_char_two (by rw [ZMod.ringChar_zmod_n]) hne]
    simp [intUnitOf]
  rw [hilbertSymbolOdd, hleg, hleg]
  norm_num

/-! ## The Legendre symbol of `-1`

The supplementary law `(-1/p) = (-1)^{(p-1)/2}`, in the form needed for the cancellation of the
`(-1/p)` factors. -/

private theorem legendreOf_neg_one_eq_neg_one_zpow {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    legendreOf p (-1) = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  have hpu : padicVal p (-1 : ℚˣ) = 0 := by rw [padicVal_neg]; simp
  have hunit : (unitPart p (-1 : ℚˣ) : ℤ_[p]) = -1 := by
    apply PadicInt.ext
    rw [unitPart_of_padicVal_eq_zero hpu]
    norm_cast
  set w : (ZMod p)ˣ := Units.map (PadicInt.toZMod (p := p)) (unitPart p (-1 : ℚˣ)) with hw
  have hw_eq : w = -1 := by
    ext
    rw [hw, Units.coe_map, hunit]
    simp
  have hq : legendreOf p (-1) = quadCharUnit p (-1) := by
    rw [legendreOf, legendreUnit, ← hw, hw_eq]
  rw [hq]
  have hq1 : quadCharUnit p (-1 : (ZMod p)ˣ) = intUnitOf (legendreSym p (-1)) := by
    rw [quadCharUnit, legendreSym]
    congr 2
    simp
  rw [hq1, legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hodd, intUnitOf_negOnePow_nat]
  rw [show p / 2 = (p - 1) / 2 by omega, zpow_natCast]

/-- `(-1)^{t²c + ct} = 1` because `t² + t = t (t+1)` is even. -/
private theorem negOne_zpow_vsq_add (t c : ℤ) : (-1 : ℤˣ) ^ (t * t * c + c * t) = 1 := by
  have he : Even (t * t * c + c * t) := by
    rw [show t * t * c + c * t = c * (t * (t + 1)) by ring]
    exact (Int.even_mul_succ_self t).mul_left c
  exact (Int.negOnePow_eq_one_iff _).mpr he

/-! ## Valuation dichotomy for `a + b = 1` -/

private theorem min_le_zero_of_add_eq_one {p : ℕ} [Fact p.Prime] {a b : ℚˣ}
    (h : (a : ℚ) + (b : ℚ) = 1) : min (padicVal p a) (padicVal p b) ≤ 0 := by
  have hsum : padicValRat p ((a : ℚ) + (b : ℚ)) = 0 := by rw [h, padicValRat.one]
  have hmin := padicValRat.min_le_padicValRat_add (p := p) (q := (a : ℚ)) (r := (b : ℚ))
    (by rw [h]; norm_num)
  rw [hsum] at hmin
  simpa only [padicVal] using hmin

private theorem min_eq_zero_of_ne_of_add_eq_one {p : ℕ} [Fact p.Prime] {a b : ℚˣ}
    (h : (a : ℚ) + (b : ℚ) = 1) (hne : padicVal p a ≠ padicVal p b) :
    min (padicVal p a) (padicVal p b) = 0 := by
  have hsum : padicValRat p ((a : ℚ) + (b : ℚ)) = 0 := by rw [h, padicValRat.one]
  have hmin := padicValRat.add_eq_min (p := p) (q := (a : ℚ)) (r := (b : ℚ))
    (by rw [h]; norm_num) a.ne_zero b.ne_zero (by simpa only [padicVal] using hne)
  rw [hsum] at hmin
  simpa only [padicVal] using hmin.symm

/-! ## The main theorem -/

theorem hilbertSymbolOdd_add_eq_one (p : ℕ) [Fact p.Prime] {a b : ℚˣ}
    (h : (a : ℚ) + (b : ℚ) = 1) : hilbertSymbolOdd p a b = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact hilbertSymbolOdd_two_eq_one a b
  by_cases heq : padicVal p a = padicVal p b
  · -- equal valuations `t`
    have hle : padicVal p a ≤ 0 := by
      have hmin := min_le_zero_of_add_eq_one (p := p) h
      rw [min_eq_left (le_of_eq heq)] at hmin
      exact hmin
    rcases lt_or_eq_of_le hle with hlt | h0
    · -- both valuations `t < 0`
      have hLL : legendreOf p a * legendreOf p b = legendreOf p (-1) :=
        legendreOf_mul_eq_legendreOf_neg_one_of_add_eq_one h heq hlt
      have hL1 : legendreOf p (-1) = (-1 : ℤˣ) ^ (((p - 1) / 2 : ℕ) : ℤ) :=
        legendreOf_neg_one_eq_neg_one_zpow hp2
      rw [hilbertSymbolOdd, ← heq, mul_assoc, ← mul_zpow, hLL, hL1, ← zpow_mul, ← zpow_add]
      exact negOne_zpow_vsq_add (padicVal p a) (((p - 1) / 2 : ℕ) : ℤ)
    · -- both valuations `0`
      exact hilbertSymbolOdd_eq_one_of_padicVal_eq_zero (p := p) (by rw [h0])
        (by rw [← heq, h0])
  · -- unequal valuations: `min = v_p(a+b) = 0`
    have hmin := min_eq_zero_of_ne_of_add_eq_one (p := p) h heq
    have hzero : padicVal p a = 0 ∨ padicVal p b = 0 := by
      rcases le_total (padicVal p a) (padicVal p b) with hle | hle
      · exact Or.inl (by rw [min_eq_left hle] at hmin; exact hmin)
      · exact Or.inr (by rw [min_eq_right hle] at hmin; exact hmin)
    rcases hzero with ha0 | hb0
    · -- `a` is a unit, `b` has positive valuation, so `a ≡ 1 (mod p)`
      have hbpos : 0 < padicVal p b := by
        rcases le_total (padicVal p a) (padicVal p b) with hle | hle
        · rw [min_eq_left hle] at hmin
          have hne : padicVal p b ≠ 0 := fun hb => heq (by rw [ha0, hb])
          omega
        · rw [min_eq_right hle] at hmin
          exact absurd (by rw [ha0, hmin] : padicVal p a = padicVal p b) heq
      have hsub : 0 < padicValRat p ((a : ℚ) - 1) := by
        have hb : (a : ℚ) - 1 = -((b : ℚ)) := by linarith
        rw [hb, padicValRat.neg]
        simpa only [padicVal] using hbpos
      have hLa : legendreOf p a = 1 :=
        legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos a ha0 hsub
      rw [hilbertSymbolOdd, ha0, hLa]
      simp
    · -- symmetric case: `b` is the unit
      have hapos : 0 < padicVal p a := by
        rcases le_total (padicVal p a) (padicVal p b) with hle | hle
        · rw [min_eq_left hle] at hmin
          exact absurd (by rw [hmin, hb0] : padicVal p a = padicVal p b) heq
        · rw [min_eq_right hle] at hmin
          have hne : padicVal p a ≠ 0 := fun ha => heq (by rw [ha, hb0])
          omega
      have hsub : 0 < padicValRat p ((b : ℚ) - 1) := by
        have ha : (b : ℚ) - 1 = -((a : ℚ)) := by linarith
        rw [ha, padicValRat.neg]
        simpa only [padicVal] using hapos
      have hLb : legendreOf p b = 1 :=
        legendreOf_eq_one_of_padicVal_eq_zero_of_sub_one_pos b hb0 hsub
      calc hilbertSymbolOdd p a b = hilbertSymbolOdd p b a := hilbertSymbolOdd_comm p a b
        _ = 1 := by rw [hilbertSymbolOdd, hb0, hLb]; simp

end Work.HilbertSymbol
