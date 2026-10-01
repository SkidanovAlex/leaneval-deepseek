import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowCoef_abs_le

/-!
# The `rowT3` estimate of the Region I row bound

`rowT3 y t r₁ = Σ_{r ≤ r₁} P_r·(γ_r² − γ_r)` with `P_r = [r ⟂ t]·μ(r)/κ(r)` and
`γ_r = log(⌊y/r⌋·r/y)` the floor defect of `y/r`.  The estimate needed by the row bound is
`|y·rowT3 y t r₁| ≤ 20·Y_t`, `Y_t = czY w y t = y·t/w`.

It is elementary: `|P_r| ≤ 1/r` (`rowCoef_abs_le`) and, since `1 ≤ r ≤ y` gives
`y/2 ≤ ⌊y/r⌋·r ≤ y`, the defect is bounded by `|γ_r| ≤ 2r/y` (`czGam_abs_le`).  Hence
`|γ_r² − γ_r| ≤ |γ_r|·(|γ_r| + 1) ≤ (2r/y)·3 = 6r/y`, so each summand is `≤ (1/r)·(6r/y) = 6/y`
and the sum is `≤ r₁·6/y ≤ 12·Y_t`.  (Note that `r₁ ≤ 2·Y_t` together with `r₁ ≥ 0` already
forces `Y_t ≥ 0`, so no other hypothesis on `w`/`t` is needed.)
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

open Finset
open Work.ZeroDensity.Jutila.LzDiffAux
open Work.ZeroDensity.Jutila.BzCross

/-- Pointwise bound for the summand of `rowT3`: for `1 ≤ r ≤ y` one has
`|P_r·(γ_r² − γ_r)| ≤ 6/y`, because `|P_r| ≤ 1/r` and `|γ_r| ≤ 2r/y`, so
`|γ_r² − γ_r| ≤ |γ_r|·(|γ_r| + 1) ≤ (2r/y)·3 = 6r/y`. -/
lemma rowT3_aux_point {y : ℝ} {t r : ℕ} (hy : 0 < y) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)| ≤ 6 / y := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  -- `|P_r| ≤ 1/r`
  have hcoef : |rowCoef t r| ≤ 1 / (r : ℝ) := rowCoef_abs_le hr
  -- `|γ_r| ≤ 2r/y`, and `2r/y ≤ 2` because `r ≤ y`
  have hgam : |rowGam y r| ≤ 2 * (r : ℝ) / y := by
    simpa only [rowGam] using czGam_abs_le hy hr hry
  have h2ry : 2 * (r : ℝ) / y ≤ 2 := by
    rw [div_le_iff₀ hy]
    linarith
  obtain ⟨hglo, hghi⟩ := abs_le.mp hgam
  -- `|γ_r − 1| ≤ |γ_r| + 1 ≤ 3`
  have hg1 : |rowGam y r - 1| ≤ 3 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- `|γ_r² − γ_r| ≤ (6/y)·r`
  have hquad : |rowGam y r ^ 2 - rowGam y r| ≤ (6 / y) * (r : ℝ) := by
    have hre : rowGam y r ^ 2 - rowGam y r = rowGam y r * (rowGam y r - 1) := by ring
    rw [hre, abs_mul]
    calc |rowGam y r| * |rowGam y r - 1| ≤ (2 * (r : ℝ) / y) * 3 :=
          mul_le_mul hgam hg1 (abs_nonneg _) (le_of_lt (div_pos (by linarith) hy))
      _ = (6 / y) * (r : ℝ) := by ring
  calc |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)|
      = |rowCoef t r| * |rowGam y r ^ 2 - rowGam y r| := abs_mul _ _
    _ ≤ (1 / (r : ℝ)) * ((6 / y) * (r : ℝ)) :=
        mul_le_mul hcoef hquad (abs_nonneg _) (le_of_lt (one_div_pos.mpr hr0))
    _ = 6 / y := by
        rw [one_div]
        rw [show (r : ℝ)⁻¹ * ((6 / y) * (r : ℝ)) = (r : ℝ)⁻¹ * (6 * (r : ℝ)) / y by ring]
        rw [show (r : ℝ)⁻¹ * (6 * (r : ℝ)) = 6 * ((r : ℝ)⁻¹ * (r : ℝ)) by ring]
        rw [inv_mul_cancel₀ hr0.ne', mul_one]

lemma rowT3_bound {w y : ℝ} {t r1 : ℕ} (hy : 0 < y)
    (hry : ∀ r ∈ Finset.Icc 1 r1, 1 ≤ r ∧ (r : ℝ) ≤ y)
    (hYy : Work.ZeroDensity.Jutila.BzCross.czY w y t ≤ y)
    (hr1 : ((r1 : ℕ) : ℝ) ≤ 2 * Work.ZeroDensity.Jutila.BzCross.czY w y t) :
    |y * Work.ZeroDensity.Jutila.LzDiffAux.rowT3 y t r1|
      ≤ 20 * Work.ZeroDensity.Jutila.BzCross.czY w y t := by
  -- `r₁ ≥ 0` and `r₁ ≤ 2·Y_t` give `0 ≤ Y_t`
  have hY0 : 0 ≤ Work.ZeroDensity.Jutila.BzCross.czY w y t := by
    have h : (0 : ℝ) ≤ (r1 : ℝ) := Nat.cast_nonneg r1
    linarith
  -- pointwise bound
  have hpt : ∀ r ∈ Finset.Icc 1 r1,
      |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)| ≤ 6 / y := by
    intro r hr
    obtain ⟨hr1', hry'⟩ := hry r hr
    exact rowT3_aux_point hy hr1' hry'
  -- summation
  have hsum : ∑ r ∈ Finset.Icc 1 r1, |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)|
      ≤ 6 * (r1 : ℝ) / y := by
    calc ∑ r ∈ Finset.Icc 1 r1, |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)|
        ≤ ∑ r ∈ Finset.Icc 1 r1, (6 / y) := Finset.sum_le_sum hpt
      _ = (r1 : ℝ) * (6 / y) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ = 6 * (r1 : ℝ) / y := by ring
  have hT3 : |rowT3 y t r1| ≤ 6 * (r1 : ℝ) / y := by
    calc |rowT3 y t r1|
        = |∑ r ∈ Finset.Icc 1 r1, rowCoef t r * (rowGam y r ^ 2 - rowGam y r)| := by
          rw [rowT3]
      _ ≤ ∑ r ∈ Finset.Icc 1 r1, |rowCoef t r * (rowGam y r ^ 2 - rowGam y r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ 6 * (r1 : ℝ) / y := hsum
  calc |y * rowT3 y t r1| = y * |rowT3 y t r1| := by rw [abs_mul, abs_of_pos hy]
    _ ≤ y * (6 * (r1 : ℝ) / y) := mul_le_mul_of_nonneg_left hT3 hy.le
    _ = 6 * (r1 : ℝ) := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ (6 * (r1 : ℝ)) hy.ne'
    _ ≤ 12 * Work.ZeroDensity.Jutila.BzCross.czY w y t := by linarith
    _ ≤ 20 * Work.ZeroDensity.Jutila.BzCross.czY w y t := by linarith

end Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux
