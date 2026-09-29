import Mathlib
import Submission.Work.CLoc.defs

namespace Work.CLoc

open Submission.CDT.LocationSing

/-- `sqM t = 1/sqP t ≤ 1/(4t+1)` for `t ≥ 0`. -/
lemma sqM_le_inv (t : ℝ) (ht : 0 ≤ t) : sqM t ≤ 1 / (4 * t + 1) := by
  rw [sqM_eq_inv t ht, inv_eq_one_div]
  apply one_div_le_one_div_of_le
  · linarith
  · exact four_mul_add_one_le_sqP t ht

/-- The "small · small" point `sqM P · sqM Q` for `999998 ≤ Q < P` is so close to `0` that
`|y| ≤ 10⁻²⁰`. -/
lemma small_small_le (P Q : ℕ) (hQ8 : (999998 : ℝ) ≤ (Q : ℝ)) (hPQ : Q < P) :
    |Submission.CDT.LocationSing.ymap
      (Submission.CDT.LocationSing.sqM (P : ℝ) * Submission.CDT.LocationSing.sqM (Q : ℝ))| ≤
      1 / 10 ^ 20 := by
  have hQnat : 999998 ≤ Q := by exact_mod_cast hQ8
  have hPnat : 999999 ≤ P := by omega
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by positivity
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hbP : sqM (P : ℝ) ≤ 1 / 3000000 := by
    refine le_trans (sqM_le_inv (P : ℝ) hP0) ?_
    apply one_div_le_one_div_of_le
    · norm_num
    · have : (999999 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPnat
      linarith
  have hbQ : sqM (Q : ℝ) ≤ 1 / 3000000 := by
    refine le_trans (sqM_le_inv (Q : ℝ) hQ0) ?_
    apply one_div_le_one_div_of_le
    · norm_num
    · have : (999998 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQnat
      linarith
  have ha0 : 0 ≤ sqM (P : ℝ) := (sqM_pos _ hP0).le
  have hb0 : 0 ≤ sqM (Q : ℝ) := (sqM_pos _ hQ0).le
  have hsmall : sqM (P : ℝ) * sqM (Q : ℝ) < (1 / 10 ^ 5 : ℝ) ^ 2 / 8 := by
    have hprod : sqM (P : ℝ) * sqM (Q : ℝ) ≤ (1 / 3000000 : ℝ) * (1 / 3000000) :=
      mul_le_mul hbP hbQ hb0 (by norm_num)
    have : (1 / 3000000 : ℝ) * (1 / 3000000) < (1 / 10 ^ 5 : ℝ) ^ 2 / 8 := by norm_num
    linarith
  have h := ymap_small_small (ε := (1 / 10 ^ 5 : ℝ)) (B := sqM (P : ℝ)) (D := sqM (Q : ℝ))
      (by norm_num) (by norm_num) (mul_nonneg ha0 hb0) hsmall
  have hfin : (1 / 10 ^ 5 : ℝ) ^ 4 / 16 ≤ 1 / 10 ^ 20 := by norm_num
  linarith

end Work.CLoc
