/-
# `Submission.Work.FIChain.zc_sharp_bounds` — the two-sided sharp bound for the truncated
outer scale `zc`

With `η_c = 1/32`, `Jc x B = ⌈log(x^{3/16}/(2(log x)^{B+2}))/log 2⌉₊`, `sc x B = 2^{Jc x B}` and
`Yc x B = √x/(sc x B·(log x)^{B+2})`, the definition `zc x B = ⌊Yc x B⌋₊` satisfies

  `x^{5/16}/2 ≤ zc x B ≤ 2·x^{5/16}`  eventually in `x`.

The upper bound is the *mirror* of the sharp lower bound `Yc_lower_sharp`: it uses
`u ≤ sc x B` (`u = x^{3/16}/(2(log x)^{B+2})`, i.e. `Nat.le_ceil` for `Jc`), which gives
`Yc x B ≤ √x/(x^{3/16}/2) = 2 x^{5/16}`, combined with `⌊Yc⌋₊ ≤ Yc`.

The lower bound uses `Yc_lower_sharp` (`x^{5/16} ≤ Yc x B`) together with
`Yc x B - 1 < ⌊Yc x B⌋₊` (`Nat.lt_floor_add_one`): since `x^{5/16} ≥ 2` for `x ≥ 16`, one has
`x^{5/16} - 1 ≥ x^{5/16}/2`.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Filter

noncomputable section

/-! ## 1. The upper half: `u ≤ sc` implies `Yc ≤ 2·x^{5/16}` -/

/-- `u = x^{1/4-2η_c}/(2(log x)^{B+2}) ≤ sc x B`, by `Nat.le_ceil` for the dyadic exponent. -/
private lemma u_le_sc_b (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) ≤ sc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
  have ht : Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
      / Real.log 2 ≤ (Jc x B : ℝ) := by rw [Jc]; exact Nat.le_ceil _
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  calc (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      = (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
          / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2) := hpow.symm
    _ ≤ (2 : ℝ) ^ ((Jc x B : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
    _ = sc x B := by rw [sc, Real.rpow_natCast]

/-- `Yc x B ≤ 2·x^{5/16}`: from `sc·(log x)^{B+2} ≥ x^{3/16}/2`. -/
private lemma Yc_upper_b (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ)) :
    Yc x B ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (by positivity)
  have hle := u_le_sc_b x B hx1
  have hden : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      * (Real.log (x : ℝ)) ^ (B + 2) := mul_pos hupos hLp_pos
  have hstep : Yc x B ≤ Real.sqrt (x : ℝ) /
      ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
        * (Real.log (x : ℝ)) ^ (B + 2)) := by
    rw [Yc]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hden
      (mul_le_mul_of_nonneg_right hle hLp_pos.le)
  have hval : (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
      * (Real.log (x : ℝ)) ^ (B + 2) = (x : ℝ) ^ ((3 : ℝ) / 16) / 2 := by
    rw [show (1 : ℝ) / 4 - 2 * etac = 3 / 16 by norm_num [etac], div_mul_eq_mul_div]
    exact mul_div_mul_right _ _ (ne_of_gt hLp_pos)
  have hval2 : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2)
      = 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have hx3 : (x : ℝ) ^ ((3 : ℝ) / 16) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hxpos _)
    have hA : Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2)
        = 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) / (x : ℝ) ^ ((3 : ℝ) / 16)) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
    rw [hA, ← Real.rpow_sub hxpos]
    congr 1
    norm_num
  calc Yc x B
      ≤ Real.sqrt (x : ℝ) /
        ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))
          * (Real.log (x : ℝ)) ^ (B + 2)) := hstep
    _ = Real.sqrt (x : ℝ) / ((x : ℝ) ^ ((3 : ℝ) / 16) / 2) := by rw [hval]
    _ = 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := hval2

/-- `0 ≤ Yc x B` for `log x > 0`. -/
private lemma Yc_nonneg_b (x : ℕ) (B : ℝ) (hL : 0 < Real.log (x : ℝ)) : 0 ≤ Yc x B := by
  rw [Yc]
  exact div_nonneg (Real.sqrt_nonneg _)
    (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (Jc x B)) (Real.rpow_pos_of_pos hL _)).le

/-! ## 2. The statement -/

theorem zc_sharp_bounds (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ ((5 : ℝ) / 16) / 2 ≤ Work.FIChain.zc x B ∧
      Work.FIChain.zc x B ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
  filter_upwards [Yc_lower_sharp B hB, eventually_ge_atTop 16] with x hYlow hx16
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hx16' : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
  -- `x^{5/16} ≥ 2` for `x ≥ 16`
  have hpow16 : (2 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := by
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 4) := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (1 : ℝ) ≤ (5 : ℝ) / 4)
      simpa using this
    have h16 : (16 : ℝ) ^ ((5 : ℝ) / 16) = (2 : ℝ) ^ ((5 : ℝ) / 4) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      norm_num
    calc (2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 4) := h2pow
      _ = (16 : ℝ) ^ ((5 : ℝ) / 16) := h16.symm
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := Real.rpow_le_rpow (by norm_num) hx16' (by norm_num)
  have hzc : zc x B = ((⌊Yc x B⌋₊ : ℕ) : ℝ) := rfl
  constructor
  · rw [hzc]
    have hlt := Nat.lt_floor_add_one (Yc x B)
    linarith
  · rw [hzc]
    calc (⌊Yc x B⌋₊ : ℝ) ≤ Yc x B := Nat.floor_le (Yc_nonneg_b x B hLpos)
      _ ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := Yc_upper_b x B hx1

end

end Work.FIChain
