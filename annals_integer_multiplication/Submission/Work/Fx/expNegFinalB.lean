import Mathlib
import Submission.Work.Fx.scaleCommon
import Submission.Work.Fx.expSubSmall

/-!
# The `exp(-x)` reduction: final field bound (variant B)

Statement requested by the `Fx` area.  Given
* `x ≥ 0` and `y = τ log 2 - x` with `|τ - x/log 2| ≤ 2` (so `y` is a small "residue"),
* `z` within `2^-(p+50)` of `y`,
* an integer `U` whose normalised value `U / 2^(2p+60)` approximates `exp z` to `4/2^(2p+60)`,
* `w = tdiv U (2^(τ+p+60))`,

we show that `w` approximates `2^p · exp(-x)` to within `2`, that `|w| ≤ 2^p`, and that `U` fits in
`2p+70` bits.

The mathematics: `exp y = 2^τ exp(-x)`, so `2^(2p+60) exp y / 2^(τ+p+60) = 2^p exp(-x)`.  Hence
`U/2^(τ+p+60)` and `2^p exp(-x)` differ by
`(2^p/2^τ)·(|U/2^(2p+60) - exp z| + |exp z - exp y|) ≤ 2^p·(4/2^(2p+60) + 8·2^-(p+50)) < 1`,
which combined with the truncation error `< 1` of `Int.tdiv` gives the first bound.  The size bound
follows from `|U|/2^(2p+60) ≤ exp z + 4/2^(2p+60) ≤ 8`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

theorem expNegFinalB (p : ℕ) (x y z : ℝ) (τ : ℕ) (U w : ℤ)
    (hp : 100 ≤ p) (hx0 : 0 ≤ x)
    (hy : y = (τ : ℝ) * Real.log 2 - x)
    (hτ : |(τ : ℝ) - x / Real.log 2| ≤ 2)
    (hzy : |z - y| ≤ 1 / 2 ^ (p + 50))
    (hU : |(U : ℝ) / 2 ^ (2 * p + 60) - Real.exp z| ≤ 4 / 2 ^ (2 * p + 60))
    (hw : w = Int.tdiv U (2 ^ (τ + p + 60))) :
    |(w : ℝ) - 2 ^ p * Real.exp (-x)| < 2 ∧ |(w : ℝ)| ≤ 2 ^ p ∧ U.natAbs.size ≤ 2 * p + 70 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h2pow : (1:ℝ) ≤ 2 := by norm_num
  have hcast2p : ((2^p : ℕ) : ℝ) = (2:ℝ)^p := by push_cast; ring
  set P : ℝ := (2:ℝ) ^ (2 * p + 60) with hP
  set D : ℝ := (2:ℝ) ^ (τ + p + 60) with hD
  have hPpos : 0 < P := by rw [hP]; positivity
  have hDpos : 0 < D := by rw [hD]; positivity
  have hPDnn : 0 ≤ P / D := le_of_lt (div_pos hPpos hDpos)
  have hU' : |(U:ℝ)/P - Real.exp z| ≤ 4/P := by rw [hP]; exact hU
  -- `exp y = 2^τ exp(-x)`
  have hy_exp : Real.exp y = (2:ℝ)^τ * Real.exp (-x) := by
    have h1 : Real.exp y = Real.exp ((τ:ℝ) * Real.log 2) * Real.exp (-x) := by
      rw [hy, sub_eq_add_neg, Real.exp_add]
    rw [h1, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hy_eq : y = Real.log 2 * ((τ:ℝ) - x / Real.log 2) := by
    rw [hy]; field_simp
  have hy_abs : |y| ≤ 2 * Real.log 2 := by
    rw [hy_eq, abs_mul, abs_of_pos hlog2pos]
    nlinarith [hτ]
  have hy_le : y ≤ 2 * Real.log 2 := le_trans (le_abs_self y) hy_abs
  have hzy1 : |z - y| ≤ 1 := by
    refine le_trans hzy ?_
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ h2pow
  -- `|z| ≤ 2`
  have hz_abs : |z| ≤ 2 := by
    have h1 : |z| ≤ |z - y| + |y| := by
      have hz' : z = (z - y) + y := by ring
      calc |z| = |(z - y) + y| := by conv_lhs => rw [hz']
        _ ≤ |z - y| + |y| := abs_add_le (z - y) y
    have hsmall : (1:ℝ) / 2 ^ (p+50) ≤ 1/2 := by
      have h : (2:ℝ) ≤ 2 ^ (p+50) := by
        calc (2:ℝ) = 2^1 := by norm_num
          _ ≤ 2^(p+50) := pow_le_pow_right₀ h2pow (by omega)
      rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
      simpa using h
    linarith
  have hexpz8 : Real.exp z ≤ 8 := by
    have h1 : Real.exp z ≤ Real.exp 2 := Real.exp_le_exp.mpr (le_trans (le_abs_self z) hz_abs)
    have h2 : Real.exp 2 < 8 := by
      have h : (2:ℝ) < Real.log 8 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
        push_cast
        nlinarith [Real.log_two_gt_d9]
      calc Real.exp 2 < Real.exp (Real.log 8) := Real.exp_lt_exp.mpr h
        _ = 8 := Real.exp_log (by norm_num)
    linarith
  have hexpdiff : |Real.exp z - Real.exp y| ≤ 8 * |z - y| := expSubSmall y z hy_le hzy1
  have hexpnegx_le : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hT_le : (2:ℝ)^p * Real.exp (-x) ≤ 2^p := by
    nlinarith [hexpnegx_le, pow_pos (by norm_num : (0:ℝ) < 2) p]
  -- the exact value of the ratio `P/D = 2^p/2^τ`
  have hratio : P / D = (2:ℝ)^p / 2^τ := by
    rw [hP, hD, div_eq_div_iff (by positivity) (by positivity), ← pow_add, ← pow_add]
    ring_nf
  have hr_le : P / D ≤ (2:ℝ)^p := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^τ := one_le_pow₀ h2pow
    have h2 : (0:ℝ) < (2:ℝ)^p := pow_pos (by norm_num) p
    calc P / D = (2:ℝ)^p / (2:ℝ)^τ := hratio
      _ ≤ (2:ℝ)^p / 1 := div_le_div_of_nonneg_left (le_of_lt h2) one_pos h1
      _ = (2:ℝ)^p := by ring
  have hT : P / D * Real.exp y = 2^p * Real.exp (-x) := by
    rw [hratio, hy_exp]; field_simp
  have hT2 : Real.exp y * (P / D) = 2^p * Real.exp (-x) := by rw [mul_comm]; exact hT
  have hterm1 : P / D * (4 / P) ≤ 1 / 2 := by
    have h1 : P / D * (4 / P) = 4 / D := by field_simp
    rw [h1, hD, div_le_div_iff₀ (by positivity) (by norm_num), one_mul]
    have h : (8:ℝ) ≤ 2^(τ+p+60) := by
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ 2^(τ+p+60) := pow_le_pow_right₀ h2pow (by omega)
    linarith
  have hterm2le : P / D * (8 * |z - y|) ≤ 8 / 2^50 := by
    have h1 : 8 * |z - y| ≤ 8 * (1 / 2^(p+50)) := by linarith [hzy]
    have h2 : P / D * (8 * |z - y|) ≤ (2:ℝ)^p * (8 * (1 / 2^(p+50))) := by
      have h8nn : 0 ≤ 8 * |z - y| := by positivity
      calc P / D * (8 * |z - y|) ≤ (2:ℝ)^p * (8 * |z - y|) := mul_le_mul_of_nonneg_right hr_le h8nn
        _ ≤ (2:ℝ)^p * (8 * (1 / 2^(p+50))) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2:ℝ)^p * (8 * (1 / 2^(p+50))) = 8 / 2^50 := by
      rw [show (2:ℝ)^(p+50) = 2^p * 2^50 by rw [pow_add]]
      field_simp
    linarith
  have hterm2le' : (8 * |z - y|) * (P / D) ≤ 8 / 2^50 := by
    rw [mul_comm]; exact hterm2le
  have hUabs_le : |(U:ℝ)|/P ≤ Real.exp z + 4/P := by
    have h1 : |(U:ℝ)/P| ≤ |(U:ℝ)/P - Real.exp z| + |Real.exp z| := by
      calc |(U:ℝ)/P| = |((U:ℝ)/P - Real.exp z) + Real.exp z| := by congr 1; ring
        _ ≤ |(U:ℝ)/P - Real.exp z| + |Real.exp z| := abs_add_le ((U:ℝ)/P - Real.exp z) (Real.exp z)
    rw [abs_div, abs_of_pos hPpos, abs_of_pos (Real.exp_pos z)] at h1
    linarith [hU']
  -- the central error bound
  have hkey : |(U:ℝ)/D - 2^p * Real.exp (-x)| < 1 := by
    have hEq : (U:ℝ)/D - 2^p * Real.exp (-x) = P/D * ((U:ℝ)/P - Real.exp y) := by
      rw [← hT]; field_simp
    rw [hEq, abs_mul, abs_of_nonneg hPDnn]
    have h2 : |(U:ℝ)/P - Real.exp y| ≤ 4/P + 8 * |z - y| := by
      calc |(U:ℝ)/P - Real.exp y| ≤ |(U:ℝ)/P - Real.exp z| + |Real.exp z - Real.exp y| :=
            abs_sub_le ((U:ℝ)/P) (Real.exp z) (Real.exp y)
        _ ≤ 4/P + 8*|z-y| := add_le_add hU' hexpdiff
    calc P/D * |(U:ℝ)/P - Real.exp y| ≤ P/D * (4/P + 8*|z-y|) := mul_le_mul_of_nonneg_left h2 hPDnn
      _ = P/D * (4/P) + P/D * (8*|z-y|) := by ring
      _ ≤ 1/2 + 8/2^50 := add_le_add hterm1 hterm2le
      _ < 1 := by norm_num
  have hUD : |(U:ℝ)|/D < 2^p + 1 := by
    have h1 : |(U:ℝ)|/D = (|(U:ℝ)|/P) * (P/D) := by field_simp
    rw [h1]
    have h2 : |(U:ℝ)|/P * (P/D) ≤ (Real.exp z + 4/P) * (P/D) :=
      mul_le_mul_of_nonneg_right hUabs_le hPDnn
    have h3 : (Real.exp z + 4/P) * (P/D) < 2^p + 1 := by
      have heq : (Real.exp z + 4/P) * (P/D) = Real.exp z * (P/D) + P/D * (4/P) := by ring
      rw [heq]
      have hzey : Real.exp z * (P/D) ≤ 2^p + 8/2^50 := by
        have h4 : Real.exp z * (P/D) = Real.exp y * (P/D) + (Real.exp z - Real.exp y) * (P/D) := by ring
        rw [h4, hT2]
        have h6 : (Real.exp z - Real.exp y) * (P/D) ≤ 8/2^50 := by
          calc (Real.exp z - Real.exp y) * (P/D) ≤ |Real.exp z - Real.exp y| * (P/D) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hPDnn
            _ ≤ (8*|z-y|) * (P/D) := mul_le_mul_of_nonneg_right hexpdiff hPDnn
            _ ≤ 8/2^50 := hterm2le'
        linarith [hT_le]
      linarith [hterm1]
    linarith
  have hUabs_lt : |(U:ℝ)| < (2:ℝ)^(2*p+70) := by
    have h1 : |(U:ℝ)| ≤ 8*P + 4 := by
      have h2 : |(U:ℝ)|/P ≤ 8 + 4/P := by linarith [hUabs_le, hexpz8]
      have h3 : |(U:ℝ)| = |(U:ℝ)|/P * P := by field_simp
      rw [h3]
      calc |(U:ℝ)|/P * P ≤ (8 + 4/P) * P := mul_le_mul_of_nonneg_right h2 (le_of_lt hPpos)
        _ = 8*P + 4 := by field_simp
    have h64 : 8*P + 4 ≤ (2:ℝ)^(2*p+64) := by
      have hPge : (1:ℝ) ≤ P := by rw [hP]; exact one_le_pow₀ h2pow
      have h16 : (16:ℝ) * P = 2^(2*p+64) := by
        rw [hP, show (16:ℝ) = 2^4 by norm_num, ← pow_add]
        congr 1; omega
      nlinarith [hPge, h16]
    have h70 : (2:ℝ)^(2*p+64) < 2^(2*p+70) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    have hDZ : (0:ℤ) < (2:ℤ)^(τ+p+60) := pow_pos (by norm_num) _
    have htd := tdiv_sub_div_lt_one U hDZ
    have hcast : (((2:ℤ)^(τ+p+60) : ℤ) : ℝ) = D := by rw [hD]; push_cast; ring
    rw [hcast] at htd
    calc |((U.tdiv ((2:ℤ)^(τ+p+60))) : ℝ) - 2^p * Real.exp (-x)|
        ≤ |((U.tdiv ((2:ℤ)^(τ+p+60))) : ℝ) - (U:ℝ)/D| + |(U:ℝ)/D - 2^p * Real.exp (-x)| :=
          abs_sub_le _ _ _
      _ < 1 + 1 := add_lt_add htd hkey
      _ = 2 := by norm_num
  · rw [hw]
    have hDZ : (0:ℤ) < (2:ℤ)^(τ+p+60) := pow_pos (by norm_num) _
    have hle := natAbs_tdiv_le_div U hDZ
    have hcast : (((2:ℤ)^(τ+p+60) : ℤ) : ℝ) = D := by rw [hD]; push_cast; ring
    rw [hcast] at hle
    have e1 : ((U.tdiv ((2:ℤ)^(τ+p+60))).natAbs : ℝ) = |((U.tdiv ((2:ℤ)^(τ+p+60))) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have e2 : ((U.natAbs : ℕ) : ℝ) = |(U:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e1, e2] at hle
    have h2 : ((U.tdiv ((2:ℤ)^(τ+p+60))).natAbs : ℝ) < (2:ℝ)^p + 1 := by
      rw [e1]; exact lt_of_le_of_lt hle hUD
    have h3 : (U.tdiv ((2:ℤ)^(τ+p+60))).natAbs ≤ 2^p := by
      have hlt : ((U.tdiv ((2:ℤ)^(τ+p+60))).natAbs : ℝ) < (((2^p + 1 : ℕ)) : ℝ) := by
        rw [show (((2^p + 1 : ℕ)) : ℝ) = (2:ℝ)^p + 1 by push_cast; ring]
        exact h2
      have := (Nat.cast_lt (α := ℝ)).mp hlt
      omega
    rw [← e1]
    calc ((U.tdiv ((2:ℤ)^(τ+p+60))).natAbs : ℝ) ≤ ((2^p : ℕ) : ℝ) := by exact_mod_cast h3
      _ = (2:ℝ)^p := hcast2p
  · rw [Nat.size_le]
    have hnat : ((U.natAbs : ℕ) : ℝ) < (2:ℝ)^(2*p+70) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hUabs_lt
    have hcast2 : ((2^(2*p+70) : ℕ) : ℝ) = (2:ℝ)^(2*p+70) := by push_cast; ring
    rw [← hcast2] at hnat
    exact_mod_cast hnat

end Work.Fx
