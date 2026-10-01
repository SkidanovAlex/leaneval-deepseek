import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Finset
open Work.ZeroDensity.Jutila.BzCross

/-! ## Elementary pointwise inputs for `rowX_bound`

The sum `rowX w y t r₁ = Σ_{r ≤ r₁} P_r·X_r·czFI w y r t` is bounded by comparing each summand
with `|log (Y_t/r)| + 1`: `|P_r| ≤ 1/r`, `|X_r| ≤ r` and `|czFI| ≤ 5(|log (Y_t/r)| + 1)`, so the
product of the first two factors is `≤ 1` and only the `czFI` estimate survives. -/

/-- `|P_r| ≤ 1/r` for the row coefficient `P_r = [r ⟂ t]·μ(r)/κ(r)`: for squarefree `r` one has
`κ(r) ≥ r`, and for non-squarefree `r` the Möbius factor vanishes. -/
lemma rowX_aux_coef_abs_le {t r : ℕ} (hr : 1 ≤ r) :
    |rowCoef t r| ≤ 1 / (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h0 : (0 : ℝ) ≤ 1 / (r : ℝ) := div_nonneg zero_le_one (le_of_lt hr0)
  have hmu1 : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  by_cases hsq : Squarefree r
  · have hk : (r : ℝ) ≤ Work.ZeroDensity.Jutila.kap r := kap_ge_self hsq
    have hkpos : (0 : ℝ) < Work.ZeroDensity.Jutila.kap r := lt_of_lt_of_le hr0 hk
    unfold rowCoef
    split_ifs with h
    · calc |(ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r|
          = |(ArithmeticFunction.moebius r : ℝ)| / Work.ZeroDensity.Jutila.kap r := by
            rw [abs_div, abs_of_pos hkpos]
        _ ≤ 1 / Work.ZeroDensity.Jutila.kap r :=
            div_le_div_of_nonneg_right hmu1 (le_of_lt hkpos)
        _ ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hr0 hk
    · rw [abs_zero]; exact h0
  · have hmu0 : ArithmeticFunction.moebius r = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    unfold rowCoef
    split_ifs with h
    · rw [hmu0]
      simp only [Int.cast_zero, zero_div, abs_zero]
      exact h0
    · rw [abs_zero]; exact h0

/-- `|X_r| ≤ r` for the floor remainder `X_r = y − r⌊y/r⌋`, when `0 < y` and `1 ≤ r ≤ y`. -/
lemma rowX_aux_rem_abs_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    |rowRem y r| ≤ (r : ℝ) := by
  have h1 : 0 ≤ rowRem y r := czX_nonneg (le_of_lt hy) hry
  have h2 : rowRem y r < (r : ℝ) := czX_lt hy hr
  rw [abs_of_nonneg h1]
  linarith

/-- `|czFI w y r t| ≤ 5(|log (Y_t/r)| + 1)`, `Y_t = y·t/w`: the `F`-factor is a bilinear expression
in `log(Y_t/r)` and the bounded floor defect `γ_r = log(C_r r/y) ∈ [−log 2, 0]`. -/
lemma rowX_aux_fi_abs_le {w y : ℝ} {r t : ℕ} (hw : 0 < w) (hr : 1 ≤ r)
    (hry : (r : ℝ) ≤ y) (ht : 1 ≤ t) :
    |czFI w y r t| ≤ 5 * (|Real.log (czY w y t / (r : ℝ))| + 1) := by
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (by exact_mod_cast hr) hry)
  have hc_le : rowGam y r ≤ 0 := czGam_le_zero hy0 hr hry
  have hc_ge : -Real.log 2 ≤ rowGam y r := czGam_neg_log_two_le hy0 hr hry
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hcabs : |rowGam y r| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  rw [rowFI_split hw hr hry ht]
  have h1 : |rowGam y r - 1| ≤ 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have h2 : |Real.log (czY w y t / (r : ℝ)) + rowGam y r - 1|
      ≤ |Real.log (czY w y t / (r : ℝ))| + 2 := by
    obtain ⟨hc1, hc2⟩ := abs_le.mp hcabs
    have hA1 := neg_abs_le (Real.log (czY w y t / (r : ℝ)))
    have hA2 := le_abs_self (Real.log (czY w y t / (r : ℝ)))
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have h5 : |(Real.log (czY w y t / (r : ℝ)) + rowGam y r - 1) * (rowGam y r - 1)|
      ≤ (|Real.log (czY w y t / (r : ℝ))| + 2) * 2 := by
    rw [abs_mul]
    exact mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
  have h6 : |(Real.log (czY w y t / (r : ℝ)) + rowGam y r - 1) * (rowGam y r - 1) + 1|
      ≤ (|Real.log (czY w y t / (r : ℝ))| + 2) * 2 + 1 := by
    have h7 := abs_add_le
      ((Real.log (czY w y t / (r : ℝ)) + rowGam y r - 1) * (rowGam y r - 1)) (1 : ℝ)
    rw [abs_one] at h7
    linarith
  have h8 : |Real.log (czY w y t / (r : ℝ))| + 2 ≤ 5 * (|Real.log (czY w y t / (r : ℝ))| + 1) := by
    have h9 := abs_nonneg (Real.log (czY w y t / (r : ℝ)))
    linarith
  linarith [h6, h8, abs_nonneg (Real.log (czY w y t / (r : ℝ)))]

lemma rowX_bound {w y : ℝ} {t r1 : ℕ} {K : ℝ} (hw : 0 < w) (ht : 1 ≤ t)
    (hry : ∀ r ∈ Finset.Icc 1 r1, 1 ≤ r ∧ (r : ℝ) ≤ y)
    (hS : ∑ r ∈ Finset.Icc 1 r1,
        (|Real.log (Work.ZeroDensity.Jutila.BzCross.czY w y t / (r : ℝ))| + 1)
      ≤ K * Work.ZeroDensity.Jutila.BzCross.czY w y t)
    (hK : 0 ≤ K) :
    |Work.ZeroDensity.Jutila.LzDiffAux.rowX w y t r1|
      ≤ 5 * K * Work.ZeroDensity.Jutila.BzCross.czY w y t := by
  have hpt : ∀ r ∈ Finset.Icc 1 r1,
      |rowCoef t r * (rowRem y r * czFI w y r t)|
        ≤ 5 * (|Real.log (czY w y t / (r : ℝ))| + 1) := by
    intro r hr
    obtain ⟨hr1, hryr⟩ := hry r hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (by exact_mod_cast hr1) hryr)
    have hc : |rowCoef t r| ≤ 1 / (r : ℝ) := rowX_aux_coef_abs_le hr1
    have hx : |rowRem y r| ≤ (r : ℝ) := rowX_aux_rem_abs_le hy0 hr1 hryr
    have hf : |czFI w y r t| ≤ 5 * (|Real.log (czY w y t / (r : ℝ))| + 1) :=
      rowX_aux_fi_abs_le hw hr1 hryr ht
    calc |rowCoef t r * (rowRem y r * czFI w y r t)|
        = |rowCoef t r| * |rowRem y r * czFI w y r t| := abs_mul _ _
      _ = |rowCoef t r| * (|rowRem y r| * |czFI w y r t|) := by rw [abs_mul]
      _ ≤ (1 / (r : ℝ)) * ((r : ℝ) * (5 * (|Real.log (czY w y t / (r : ℝ))| + 1))) :=
          mul_le_mul hc (mul_le_mul hx hf (abs_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = 5 * (|Real.log (czY w y t / (r : ℝ))| + 1) := by
          rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hrpos)]
  have hsum : ∑ r ∈ Finset.Icc 1 r1, |rowCoef t r * (rowRem y r * czFI w y r t)|
      ≤ 5 * ∑ r ∈ Finset.Icc 1 r1, (|Real.log (czY w y t / (r : ℝ))| + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpt
  calc |Work.ZeroDensity.Jutila.LzDiffAux.rowX w y t r1|
      = |∑ r ∈ Finset.Icc 1 r1, rowCoef t r * (rowRem y r * czFI w y r t)| := by
        rw [Work.ZeroDensity.Jutila.LzDiffAux.rowX]
    _ ≤ ∑ r ∈ Finset.Icc 1 r1, |rowCoef t r * (rowRem y r * czFI w y r t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ 5 * ∑ r ∈ Finset.Icc 1 r1, (|Real.log (czY w y t / (r : ℝ))| + 1) := hsum
    _ ≤ 5 * (K * czY w y t) := by linarith
    _ = 5 * K * czY w y t := by ring

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
