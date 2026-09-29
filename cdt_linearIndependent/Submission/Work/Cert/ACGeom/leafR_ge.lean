import Mathlib
import Submission.Work.Cert.Spec

/-! # The leaf radius dominates the chord half-length plus the `ETOL` slack

`leafR L = leafRz L / S` is the radius (in units of `S`) of the input disc of the leaf `L`, with

`leafRz L = ⌊chU/2⌋ + 1 + ⌈(⌈chU·chU/S⌉ · S) / (2 Rk k)⌉ + 1 + ETOL`.

Geometrically (see `Work/Cert/arc_cover.lean`) this disc is meant to contain the circle arc between
`A = (L.Ax + i·L.Ay)/S` and `B = (L.Bx + i·L.By)/S`; the first requirement is that it at least
contains the point `(A+B)/2`, whose distance from `leafC L` is at most `chU/(2S) + 1/S`, whence the
radius must be at least `(chU/2 + ETOL − 1)/S`. This file proves that arithmetic inequality.

All that is used is that `Int.ediv` is a floor:
* `⌊a/2⌋ > a/2 − 1` always (`Int.lt_ediv_add_one_mul_self`),
* `mu chU chU = ⌈chU²/S⌉ ≥ 0` and `dvu x y = ⌈x·S/y⌉ ≥ 0` for `x ≥ 0 < y`.

The two `+1`s in `leafRz` are far more than the two floors need. -/

namespace Work.Cert.ACGeom

open Work.Cert

/-! ## Elementary integer rounding facts -/

lemma S_pos_z : (0 : ℤ) < S := by norm_num [S]

lemma S_pos_R : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos_z

/-- a floor of a non-positive integer, divided by a positive one, is `≤ 0`. -/
lemma ediv_nonpos_of_nonpos {x b : ℤ} (hx : x ≤ 0) (hb : 0 < b) : Int.ediv x b ≤ 0 := by
  have hq : Int.ediv x b * b ≤ x := Int.ediv_mul_le _ (ne_of_gt hb)
  exact (mul_le_mul_iff_of_pos_right hb).mp (by simpa using le_trans hq hx)

/-- the circle radii `Rk k` are positive. -/
lemma Rk_pos (k : ℕ) : 0 < Rk k := by
  rw [Rk]
  split_ifs with h1 h2
  · norm_num [fdiv, S]
  · norm_num [fdiv, S]
  · exact S_pos_z

/-- `mu a b = ⌈a·b/S⌉` is non-negative for non-negative `a`, `b`. -/
lemma mu_nonneg (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mu a b := by
  rw [mu, fdiv]
  exact neg_nonneg.mpr (ediv_nonpos_of_nonpos (neg_nonpos.mpr (mul_nonneg ha hb)) S_pos_z)

/-- `dvu a b = ⌈a·S/b⌉` is non-negative for `a ≥ 0 < b`. -/
lemma dvu_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ dvu a b := by
  rw [dvu, fdiv]
  exact neg_nonneg.mpr
    (ediv_nonpos_of_nonpos (neg_nonpos.mpr (mul_nonneg ha (le_of_lt S_pos_z))) hb)

/-- the floor of `a/2` is `> a/2 − 1`. -/
lemma ediv_two_cast_gt (a : ℤ) : (a : ℝ) / 2 - 1 < ((Int.ediv a 2 : ℤ) : ℝ) := by
  have hh : a < (Int.ediv a 2 + 1) * 2 := Int.lt_ediv_add_one_mul_self a (by norm_num)
  have hh2 : (a : ℝ) < (((Int.ediv a 2 : ℤ) : ℝ) + 1) * 2 := by exact_mod_cast hh
  linarith

/-! ## The radius bound -/

theorem leafR_ge (L : Leaf) (h : (0 : ℝ) ≤ L.chU) :
    ((L.chU : ℝ) / 2 + (ETOL : ℝ) - 1) / (S : ℝ) ≤ leafR L := by
  rw [leafR, div_le_div_iff_of_pos_right S_pos_R]
  change ((L.chU : ℝ) / 2 + (ETOL : ℝ) - 1) ≤
    ((Int.ediv L.chU 2 + 1 + dvu (mu L.chU L.chU) (2 * Rk L.k) + 1 + ETOL : ℤ) : ℝ)
  have hchU : (0 : ℤ) ≤ L.chU := by exact_mod_cast h
  have hdiv : (L.chU : ℝ) / 2 - 1 < ((Int.ediv L.chU 2 : ℤ) : ℝ) := ediv_two_cast_gt L.chU
  have hmu : 0 ≤ mu L.chU L.chU := mu_nonneg L.chU L.chU hchU hchU
  have hRk : 0 < 2 * Rk L.k := by have := Rk_pos L.k; omega
  have hdvu : (0 : ℝ) ≤ ((dvu (mu L.chU L.chU) (2 * Rk L.k) : ℤ) : ℝ) := by
    have := dvu_nonneg hmu hRk
    exact_mod_cast this
  push_cast
  linarith

end Work.Cert.ACGeom
