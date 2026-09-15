import Submission.Work.GYCorr8

/-!
# `GYCorr9`: the balanced representative of a residue and the window lift

This file contains the two combinatorial/arithmetic inputs needed to turn the correlation
condition `𝔼_x ∏_i ν(x+h_i) ≤ Σ_{i<j}τ(h_i-h_j)` into a *box average* of the degenerate system
`x ↦ W(x+h_i)+1` (Green–Tao Proposition GY2 = `boxAvgCorr_ub'`):

* `bal : ZMod p → ℤ`, the balanced representative, with `(bal z : ZMod p) = z` and
  `|bal z| = min z.val (p - z.val)`;
* the **window lift**: if all `x + h i` (`i ∈ A`) lie in the window `[εp, 2εp]`, then
  `(x + h i).val = (x + h i₀).val + bal (h i - h i₀)`.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

variable {p : ℕ} [NeZero p]

/-! ## 1. The balanced representative of a residue -/

/-- The balanced representative of `z : ZMod p`, i.e. the unique `b` with `(b : ZMod p) = z` and
`2|b| ≤ p`. -/
def bal (z : ZMod p) : ℤ := if 2 * z.val ≤ p then (z.val : ℤ) else (z.val : ℤ) - p

lemma bal_cast (z : ZMod p) : ((bal z : ℤ) : ZMod p) = z := by
  rw [bal]
  split_ifs with h
  · push_cast
    exact ZMod.natCast_zmod_val z
  · push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, sub_zero]

lemma abs_bal_eq_min (z : ZMod p) :
    |bal z| = min (z.val : ℤ) ((p : ℤ) - (z.val : ℤ)) := by
  have hzv : z.val ≤ p := le_of_lt (ZMod.val_lt z)
  have hcast : ((p - z.val : ℕ) : ℤ) = (p : ℤ) - (z.val : ℤ) := by
    push_cast [Nat.cast_sub hzv]
    ring
  rw [bal]
  split_ifs with h
  · have h2 : (z.val : ℤ) ≤ (p : ℤ) - (z.val : ℤ) := by
      have : 2 * z.val ≤ p := h
      omega
    rw [abs_of_nonneg (by positivity), min_eq_left h2]
  · have h2 : (p : ℤ) - (z.val : ℤ) ≤ (z.val : ℤ) := by omega
    have hle : (z.val : ℤ) - p ≤ 0 := by omega
    rw [abs_of_nonpos hle, min_eq_right h2]
    ring

lemma two_mul_abs_bal_le (z : ZMod p) : 2 * |bal z| ≤ (p : ℤ) := by
  rw [abs_bal_eq_min]
  have h1 : min (z.val : ℤ) ((p : ℤ) - (z.val : ℤ)) ≤ (z.val : ℤ) := min_le_left _ _
  have h2 : min (z.val : ℤ) ((p : ℤ) - (z.val : ℤ)) ≤ (p : ℤ) - (z.val : ℤ) :=
    min_le_right _ _
  linarith

/-! ## 2. Integer arithmetic: `a ≡ b (mod p)`, `|a| + |b| < p` ⟹ `a = b` -/

lemma eq_of_abs_add_abs_lt_of_intCast_eq' {a b : ℤ}
    (h : (a : ZMod p) = (b : ZMod p)) (hab : |a| + |b| < (p : ℤ)) : a = b := by
  have hdvd : (p : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp h
  have h1 : |b - a| ≤ |a| + |b| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]
  have h2 : |b - a| < (p : ℤ) := lt_of_le_of_lt h1 hab
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    by_contra hkne
    have h3 : (1 : ℤ) ≤ |k| := Int.one_le_abs (by omega)
    have h4 : |b - a| = (p : ℤ) * |k| := by
      rw [show b - a = (p : ℤ) * k from hk, abs_mul, abs_of_nonneg (by positivity)]
    have hp1 : (1 : ℤ) ≤ (p : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    nlinarith [h3, h4, h2, hp1]
  rw [hk0, mul_zero] at hk
  omega

/-! ## 3. The window lift -/

variable {m : ℕ}

/-- **The window lift.**  If all the residues `x + h i` (`i ∈ A`) lie in the window
`[εp, 2εp]`, then the natural representative of `x + h i` is obtained from that of `x + h i₀` by
adding the balanced representative `bal (h i - h i₀)`:

`(x + h i).val = (x + h i₀).val + bal (h i - h i₀)`.

This is the change of variables which turns the `ZMod p` sum of the correlation condition into the
box sum of Green–Tao's Proposition GY2. -/
lemma val_add_eq_of_window {h : Fin m → ZMod p} {A : Finset (Fin m)} {i₀ : Fin m} {ε : ℝ}
    (hε0 : 0 < ε) (hε4 : 4 * ε ≤ 1) {x : ZMod p} (hi₀ : i₀ ∈ A)
    (hlo : ∀ i ∈ A, ε * (p : ℝ) ≤ ((x + h i).val : ℝ))
    (hhi : ∀ i ∈ A, ((x + h i).val : ℝ) ≤ 2 * ε * (p : ℝ))
    {i : Fin m} (hi : i ∈ A) :
    ((x + h i).val : ℤ) = ((x + h i₀).val : ℤ) + bal (h i - h i₀) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_neZero p
  -- the congruence
  have hcong : ((((x + h i).val : ℤ) - ((x + h i₀).val : ℤ) : ℤ) : ZMod p)
      = bal (h i - h i₀) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, bal_cast]
    ring
  -- size bounds
  have ha_ub : ((x + h i).val : ℤ) - ((x + h i₀).val : ℤ) ≤ ⌊ε * (p : ℝ)⌋ := by
    refine Int.le_floor.mpr ?_
    push_cast
    linarith [hhi i hi, hlo i₀ hi₀]
  have ha_lb : -(((x + h i).val : ℤ) - ((x + h i₀).val : ℤ)) ≤ ⌊ε * (p : ℝ)⌋ := by
    refine Int.le_floor.mpr ?_
    push_cast
    linarith [hhi i₀ hi₀, hlo i hi]
  have ha : |((x + h i).val : ℤ) - ((x + h i₀).val : ℤ)| ≤ ⌊ε * (p : ℝ)⌋ := by
    rw [abs_le]
    exact ⟨by linarith, ha_ub⟩
  -- `2|a| ≤ ⌊p/2⌋`, `2|b| ≤ p`
  have hmid : 2 * ⌊ε * (p : ℝ)⌋ ≤ ⌊(p : ℝ) / 2⌋ := by
    refine Int.le_floor.mpr ?_
    have h3 : ((⌊ε * (p : ℝ)⌋ : ℤ) : ℝ) ≤ ε * (p : ℝ) := Int.floor_le _
    push_cast
    nlinarith [h3, hpR, hε0, hε4]
  have h2a : 2 * |((x + h i).val : ℤ) - ((x + h i₀).val : ℤ)| ≤ ⌊(p : ℝ) / 2⌋ := by
    linarith [ha, hmid]
  have h2b : 2 * |bal (h i - h i₀)| ≤ (p : ℤ) := two_mul_abs_bal_le _
  have hp2 : ⌊(p : ℝ) / 2⌋ < (p : ℤ) := by
    refine Int.floor_lt.mpr ?_
    push_cast
    nlinarith [hpR]
  have hsum : |((x + h i).val : ℤ) - ((x + h i₀).val : ℤ)| + |bal (h i - h i₀)| < (p : ℤ) := by
    have h := add_le_add h2a h2b
    linarith [h, hp2]
  have hfin := eq_of_abs_add_abs_lt_of_intCast_eq' hcong hsum
  omega

end Corr
end GYMaj
