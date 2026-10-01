import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Work.ZeroDensity.Jutila.BzCross
open Work.ZeroDensity.Jutila.LzDiffAux

/-- Pointwise bound for the `F`-factor of Region I: with `C = ⌊y/r⌋`, `γ = log(C r/y)` and
`Y = czY w y t = y t/w` one has `czFI w y r t = (log(Y/r) + γ - 1)(γ - 1) + 1`, while
`1 ≤ r ≤ y` forces `/2 ≤ C r/y ≤ 1`, i.e. `-log 2 ≤ γ ≤ 0`, so `|γ - 1| ≤ 1 + log 2 ≤ 2`.
Hence `|czFI| ≤ |log(Y/r)|·(1+log 2) + (1+log 2)² + 1 ≤ 5(|log(Y/r)| + 1)`. -/
lemma rowFI_abs_le {w y : ℝ} {r t : ℕ} (hw : 0 < w) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y) (ht : 1 ≤ t) :
    |Work.ZeroDensity.Jutila.BzCross.czFI w y r t|
      ≤ 5 * (|Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r : ℝ))| + 1) := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans hr1 hry)
  have hC1 : 1 ≤ ⌊y / (r:ℝ)⌋₊ := czCr_ge_one hry hr
  have hCy_pos : 0 < ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊y / (r:ℝ)⌋₊)
  -- `⌊y/r⌋ · r ≤ y`
  have hCr_le : ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) ≤ y := by
    have h := Nat.floor_le (show (0:ℝ) ≤ y / (r:ℝ) by positivity)
    calc ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ)
        ≤ (y / (r:ℝ)) * (r:ℝ) := mul_le_mul_of_nonneg_right h hr0.le
      _ = y := by field_simp
  -- `y/2 ≤ ⌊y/r⌋ · r`
  have hCr_ge : y/2 ≤ ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) := by
    by_cases h : (r:ℝ) ≤ y/2
    · have hlt := Nat.lt_floor_add_one (y / (r:ℝ))
      have h2 : y / (r:ℝ) - 1 < ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) := by linarith
      have h3 : (y / (r:ℝ) - 1) * (r:ℝ) < ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) :=
        mul_lt_mul_of_pos_right h2 hr0
      have h4 : (y / (r:ℝ) - 1) * (r:ℝ) = y - (r:ℝ) := by
        rw [sub_mul, div_mul_cancel₀ y hr0.ne', one_mul]
      linarith
    · simp only [not_le] at h
      have hC1' : (1:ℝ) ≤ ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hC1
      have h5 : (1:ℝ) * (r:ℝ) ≤ ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) :=
        mul_le_mul_of_nonneg_right hC1' hr0.le
      linarith
  have hfrac_pos : 0 < ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) / y :=
    div_pos (mul_pos hCy_pos hr0) hy0
  have hfrac_le1 : ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) / y ≤ 1 := by
    rw [div_le_one hy0]; exact hCr_le
  have hfrac_ge : (1:ℝ)/2 ≤ ((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) / y := by
    rw [le_div_iff₀ hy0]; linarith
  -- `-log 2 ≤ γ ≤ 0`
  have hgle : rowGam y r ≤ 0 := by
    unfold rowGam
    have h := Real.log_le_log hfrac_pos hfrac_le1
    rwa [Real.log_one] at h
  have hgge : -Real.log 2 ≤ rowGam y r := by
    unfold rowGam
    have h12 : Real.log ((1:ℝ)/2) ≤ Real.log (((⌊y / (r:ℝ)⌋₊ : ℕ) : ℝ) * (r:ℝ) / y) :=
      Real.log_le_log (by norm_num) hfrac_ge
    have hloghalf : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
    linarith
  have hgm : |rowGam y r - 1| ≤ 1 + Real.log 2 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    constructor <;> linarith
  set m : ℝ := 1 + Real.log 2 with hm
  have hm_nonneg : 0 ≤ m := by
    rw [hm]; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
  have hm2 : m ≤ 2 := by
    rw [hm]; have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  -- the pointwise splitting `czFI = (L + γ - 1)(γ - 1) + 1`
  have hsplit := rowFI_split (w:=w) (y:=y) (r:=r) (t:=t) hw hr hry ht
  have hA : Work.ZeroDensity.Jutila.BzCross.czFI w y r t
      = Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ)) * (rowGam y r - 1)
        + (rowGam y r - 1)^2 + 1 := by
    rw [hsplit]; ring
  rw [hA]
  have h1 : |Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ)) * (rowGam y r - 1)|
      ≤ |Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ))| * m := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by rw [hm]; exact hgm) (abs_nonneg _)
  have h2 : |(rowGam y r - 1)^2| ≤ m^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [hm]; exact hgm) 2
  have h3 := abs_add_three (Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ))
      * (rowGam y r - 1)) ((rowGam y r - 1)^2) 1
  rw [abs_one] at h3
  have hstep : |Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ)) * (rowGam y r - 1)
      + (rowGam y r - 1)^2 + 1|
      ≤ |Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ))| * m + m^2 + 1 := by
    linarith
  refine le_trans hstep ?_
  have hL := abs_nonneg (Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r:ℝ)))
  nlinarith [hm_nonneg, hm2, hL]

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
