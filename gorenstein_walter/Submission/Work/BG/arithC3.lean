/-
Arithmetic leaf **AR-C3** of the Bender–Glauberman Theorem C chain (see
`Submission/Work/BG/ThmABCDefs.lean`, section 8, and
`Submission/Work/NOTES_LEAD_gw_design16.md` §4).

Route (BG pp. 210–211, (6)+(7)+Lemma 2.5), with `c := 8A+1`:

* every term of the identity (6) is bounded by `/(8A+1)` using `|dᵢ| ≥ 8A+1`:
  `2k²/N ≤ (2x²+6)/c`;
* Lemma 2.5 gives `2k²/N > 1 - 3/|φ(1)| ≥ 1 - 3/c`;
* hence `c - 3 < 2x²+6`, i.e. `4A - 4 < x²`;
* `x = 0` then forces `A < 1`, contradicting `1 ≤ A`;
* `x ≠ 0` gives `x² ≤ 2b` and `b ≤ A` (Frobenius), so `4A - 4 < x² ≤ 2b ≤ 2A`,
  forcing `A < 2` — while `b ≤ A` and `2 ≤ b` give `2 ≤ A`.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

namespace ArithC3Aux

/-- With `0 < c ≤ |d|` and `0 ≤ a`, dividing by `d` can only help: `a/d ≤ a/c`. -/
lemma div_le_div_of_abs_le {a : ℚ} (ha : 0 ≤ a) {c d : ℚ} (hc : 0 < c) (h : c ≤ |d|) :
    a / d ≤ a / c := by
  rcases le_or_gt 0 d with hd | hd
  · have hcd : c ≤ d := by rwa [abs_of_nonneg hd] at h
    exact div_le_div_of_nonneg_left ha hc hcd
  · have h1 : a / d ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha (le_of_lt hd)
    have h2 : 0 ≤ a / c := div_nonneg ha (le_of_lt hc)
    linarith

/-- With `0 < c ≤ |d|`, the negative term `-4/d` of the identity (6) is at most `4/c`. -/
lemma neg_four_div_le {c d : ℚ} (hc : 0 < c) (h : c ≤ |d|) : -(4 / d) ≤ 4 / c := by
  rcases le_or_gt 0 d with hd | hd
  · have h1 : -(4 / d) ≤ 0 := by
      have : 0 ≤ 4 / d := div_nonneg (by norm_num) hd
      linarith
    have h2 : 0 ≤ (4:ℚ) / c := div_nonneg (by norm_num) (le_of_lt hc)
    linarith
  · have hd' : |d| = -d := abs_of_neg hd
    rw [hd'] at h
    have hneg : -(4 / d) = 4 / (-d) := by field_simp
    rw [hneg]
    exact div_le_div_of_nonneg_left (by norm_num) hc h

/-- Transport of the integral degree bound `8A+1 ≤ |d|` to `ℚ`. -/
lemma cast_bound {A : ℕ} {d : ℤ} (h : 8 * (A : ℤ) + 1 ≤ |d|) :
    8 * (A : ℚ) + 1 ≤ |(d : ℚ)| := by
  have h' : ((8 * (A : ℤ) + 1 : ℤ) : ℚ) ≤ ((|d| : ℤ) : ℚ) := by exact_mod_cast h
  rw [Int.cast_abs] at h'
  push_cast at h'
  exact h'

end ArithC3Aux

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem arithC3 : Work.GW2.C16.ArithC3Prop := by
  intro N k A b x d1 d2 d3 dφ hN hA hb hd1 hd2 hd3 hdφ hineq heq hxb
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hAq : (1 : ℚ) ≤ (A : ℚ) := by exact_mod_cast hA
  have hbq : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hcpos : (0 : ℚ) < 8 * (A : ℚ) + 1 := by linarith
  have hd1c : 8 * (A : ℚ) + 1 ≤ |(d1 : ℚ)| := ArithC3Aux.cast_bound hd1
  have hd2c : 8 * (A : ℚ) + 1 ≤ |(d2 : ℚ)| := ArithC3Aux.cast_bound hd2
  have hd3c : 8 * (A : ℚ) + 1 ≤ |(d3 : ℚ)| := ArithC3Aux.cast_bound hd3
  have hdφc : 8 * (A : ℚ) + 1 ≤ |(dφ : ℚ)| := ArithC3Aux.cast_bound hdφ
  set c : ℚ := 8 * (A : ℚ) + 1 with hcdef
  -- upper bound for the right-hand side `2k²/N` of (6): each term is `≤ /(8A+1)`
  have hE : (1 + (x:ℚ))^2 / (d1:ℚ) + (1 - (x:ℚ))^2 / (d2:ℚ) - 4/(d3:ℚ)
      ≤ (2*(x:ℚ)^2 + 6)/c := by
    have h1 := ArithC3Aux.div_le_div_of_abs_le (a := (1 + (x:ℚ))^2) (sq_nonneg _) hcpos hd1c
    have h2 := ArithC3Aux.div_le_div_of_abs_le (a := (1 - (x:ℚ))^2) (sq_nonneg _) hcpos hd2c
    have h3 := ArithC3Aux.neg_four_div_le (c := c) (d := (d3:ℚ)) hcpos hd3c
    have hsum : (1 + (x:ℚ))^2/c + (1 - (x:ℚ))^2/c + 4/c = (2*(x:ℚ)^2+6)/c := by ring
    linarith
  -- lower bound from Lemma 2.5: `2k²/N > 1 - 3/|φ(1)| ≥ 1 - 3/c`
  have hNle : (N:ℚ) * (1 - 3/c) ≤ (N:ℚ) * (1 - 3/|(dφ:ℚ)|) := by
    have h3c : 3 / |(dφ : ℚ)| ≤ 3 / c :=
      div_le_div_of_nonneg_left (by norm_num) hcpos hdφc
    have : (1:ℚ) - 3/c ≤ 1 - 3/|(dφ:ℚ)| := by linarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hNq)
  have hlt : (N:ℚ) * (1 - 3/c) < (N:ℚ) * ((2*(x:ℚ)^2+6)/c) := by
    have h4 : (N:ℚ) * ((1 + (x:ℚ))^2/(d1:ℚ) + (1 - (x:ℚ))^2/(d2:ℚ) - 4/(d3:ℚ))
        ≤ (N:ℚ) * ((2*(x:ℚ)^2+6)/c) := mul_le_mul_of_nonneg_left hE (le_of_lt hNq)
    linarith [heq]
  have hdiv : (1:ℚ) - 3/c < (2*(x:ℚ)^2 + 6)/c := (mul_lt_mul_iff_of_pos_left hNq).mp hlt
  -- clear denominators and unfold `c = 8A+1`
  have hmain : 4*(A:ℚ) - 4 < (x:ℚ)^2 := by
    have h := mul_lt_mul_of_pos_left hdiv hcpos
    have e1 : c * (1 - 3/c) = c - 3 := by field_simp
    have e2 : c * ((2*(x:ℚ)^2 + 6)/c) = 2*(x:ℚ)^2 + 6 := by field_simp
    rw [e1, e2] at h
    rw [hcdef] at h
    linarith
  by_cases hx : x = 0
  · -- `x = 0` forces `A < 1`
    rw [hx] at hmain
    push_cast at hmain
    linarith
  · -- `x ≠ 0`: Frobenius gives `x² ≤ 2b`, `b ≤ A`
    have hxb' := hxb hx
    have hx2b : (x:ℚ)^2 ≤ 2*(b:ℚ) := by exact_mod_cast hxb'.1
    have hbA : (b:ℚ) ≤ (A:ℚ) := by exact_mod_cast hxb'.2
    linarith

end Work.BG
