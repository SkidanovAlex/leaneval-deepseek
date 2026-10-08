/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# Bender's Case 1: the arithmetic endgame

The integer part of Bender's §3 Case 1: with `a = |C_G(X)|`, `b_n` the number of nontrivial
cosets of `H = C_G(X)⟨t⟩` containing exactly `n` involutions, `|J|` the number of involutions of
`G` and `|G| = 8|J|`, the relations

* `|J| = a + b_1 + 2 b_2` (counting involutions inside and outside `H`),
* `|G : H| = 1 + b_0 + b_1 + b_2` (counting nontrivial cosets),
* `|J| · 4 = |G : H| · a` (orbit–stabiliser: `|G| = |G:H| · 2a`),
* `3 ∣ a`, `a` odd, `a ≠ 3`, and
* `b_2 = 2a`  (Bender's double count)

force `a = 9`, `b_1 = 0`, `b_0 = 1`, `|J| = 45` and `|G| = 360`.
-/
import Mathlib

namespace Work.BSW.Cases.K4

/-- Bender's Case 1 arithmetic: the relations listed in the module docstring force `|G| = 360`. -/
theorem case1_arith {a b0 b1 b2 idx cardJ cardG : ℕ}
    (ha3 : 3 ∣ a) (hane : a ≠ 3) (haodd : Odd a)
    (hJ : cardJ = a + b1 + 2 * b2)
    (hidx : idx = 1 + b0 + b1 + b2)
    (h4 : cardJ * 4 = idx * a)
    (hb2 : b2 = 2 * a)
    (hG : cardG = 8 * cardJ) :
    cardG = 360 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at haodd
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  -- `a ≥ 9`: `a = 3 m` with `m` odd and `≠ 1`
  have ha9 : 9 ≤ a := by
    obtain ⟨m, hm⟩ := ha3
    have hm_ne1 : m ≠ 1 := by
      rintro rfl
      exact hane hm
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm
        exact absurd hm ha0
      · exact h
    have hm_ne2 : m ≠ 2 := by
      rintro rfl
      rw [hm] at haodd
      norm_num at haodd
    omega
  -- the polynomial relation
  have h0 : 20 * a + 4 * b1 = a + a * b0 + a * b1 + 2 * a * a := by
    have h := h4
    rw [hJ, hidx, hb2] at h
    nlinarith [h]
  -- `a ∣ 4 b1` and hence `a ∣ b1`
  have hdvd : a ∣ 4 * b1 := by
    have h2 : a ∣ 20 * a + 4 * b1 := ⟨1 + b0 + b1 + 2 * a, by rw [h0]; ring⟩
    have hsub : 4 * b1 = (20 * a + 4 * b1) - 20 * a := by omega
    have h3 : a ∣ (20 * a + 4 * b1) - 20 * a := Nat.dvd_sub h2 ⟨20, by ring⟩
    rwa [← hsub] at h3
  have hcop : Nat.Coprime a 4 := by
    have h2 : Nat.Coprime a 2 := Nat.coprime_two_right.mpr haodd
    simpa using h2.pow_right 2
  have hdvd1 : a ∣ b1 := by
    have := hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    exact this
  obtain ⟨k, hk⟩ := hdvd1
  -- cancel `a` and finish
  have h3 : 20 + 4 * k = 1 + b0 + a * k + 2 * a := by
    have h1 : 20 * a + 4 * (a * k) = a + a * b0 + a * (a * k) + 2 * a * a := by
      rw [← hk]; exact h0
    have h2 : a * (20 + 4 * k) = a * (1 + b0 + a * k + 2 * a) := by
      nlinarith [h1]
    exact Nat.mul_left_cancel hapos h2
  have hb0k : a * k + 2 * a + b0 = 19 + 4 * k := by omega
  have ha_le : a ≤ 9 := by
    have hak : a * k = (a - 4) * k + 4 * k := by
      rw [← add_mul, Nat.sub_add_cancel (by omega : 4 ≤ a)]
    rw [hak] at hb0k
    omega
  have ha : a = 9 := by omega
  subst ha
  have hk0 : k = 0 := by omega
  subst hk0
  have hb0 : b0 = 1 := by omega
  have hb1 : b1 = 0 := by omega
  have hJ45 : cardJ = 45 := by omega
  omega

end Work.BSW.Cases.K4
