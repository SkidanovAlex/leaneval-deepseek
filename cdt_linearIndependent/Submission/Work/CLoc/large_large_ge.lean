import Mathlib
import Submission.Work.CLoc.defs

namespace Work.CLoc

open Submission.CDT.LocationSing (sqP sqM ymap sqP_pos four_mul_add_one_le_sqP
  ymap_large_large)

/-- For `999998 ≤ Q < P` the "large · large" singularity satisfies
`|y (sqP P · sqP Q)| ≥ 900000`: `sqP P ≥ 4P+1 ≥ 3999997 > 10⁶`, so `ymap_large_large`
(with `ε = 10⁻⁶`) gives `10⁶ < |y|`. -/
lemma large_large_ge (P Q : ℕ) (hQ8 : (999998 : ℝ) ≤ (Q : ℝ)) (hPQ : Q < P) :
    900000 ≤ |Submission.CDT.LocationSing.ymap
      (Submission.CDT.LocationSing.sqP (P : ℝ) * Submission.CDT.LocationSing.sqP (Q : ℝ))| := by
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by linarith
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by
    have h : ((Q : ℝ)) ≤ (P : ℝ) := by exact_mod_cast le_of_lt hPQ
    linarith
  have hCP1 : (999999 : ℝ) ≤ (P : ℝ) := by
    have h1 : ((Q : ℝ) + 1) ≤ (P : ℝ) := by
      have : Q + 1 ≤ P := hPQ
      exact_mod_cast this
    linarith
  have hAlow : 4 * (P : ℝ) + 1 ≤ sqP (P : ℝ) := four_mul_add_one_le_sqP _ hP0
  have hClow : 4 * (Q : ℝ) + 1 ≤ sqP (Q : ℝ) := four_mul_add_one_le_sqP _ hQ0
  have hA1 : (1000000 : ℝ) < sqP (P : ℝ) := by linarith
  have hC1 : (1 : ℝ) ≤ sqP (Q : ℝ) := by linarith
  have hAC : (1 : ℝ) / (1 / 10 ^ 6) < sqP (P : ℝ) * sqP (Q : ℝ) := by
    have hgt : (1000000 : ℝ) < sqP (P : ℝ) * sqP (Q : ℝ) := by
      have hpos : (0 : ℝ) < sqP (P : ℝ) := by linarith
      calc (1000000 : ℝ) = 1000000 * 1 := by ring
        _ < sqP (P : ℝ) * sqP (Q : ℝ) :=
          mul_lt_mul hA1 hC1 (by norm_num) (le_of_lt hpos)
    have hsimp : (1 : ℝ) / (1 / 10 ^ 6) = 1000000 := by norm_num
    linarith
  have h := ymap_large_large (A := sqP (P : ℝ)) (C := sqP (Q : ℝ)) (ε := 1 / 10 ^ 6)
    (by norm_num) (by norm_num) hAC
  have h1000000 : (1 : ℝ) / (1 / 10 ^ 6) = 1000000 := by norm_num
  rw [h1000000] at h
  linarith

end Work.CLoc
