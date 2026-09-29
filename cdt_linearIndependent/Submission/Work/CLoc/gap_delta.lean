import Mathlib
import Submission.Work.CLoc.defs

/-!
# The relative gap of `sqP`

With `d := P - Q`, `q := Q ≥ 1`, and the hypothesis `d ≤ q ε (1 + 2ε)`, `ε = 10⁻⁶`, we show
`(sqP P − sqP Q)/sqP Q ≤ 1.0005·10⁻⁶`.

The proof is a three-step chain of elementary estimates:

* `sqP_sub_sqP_le`: `sqP P − sqP Q ≤ 2 d (2 + 1/(2q+1))`;
* `four_mul_add_one_le_sqP`: `sqP Q ≥ 4q + 1`, so dividing by the smaller denominator is safe;
* `2 (2 + 1/(2q+1)) ≤ (4q + 1)/q`, so the result is at most `d/q ≤ ε(1 + 2ε) ≤ 1.0005 ε`.
-/

namespace Work.CLoc

open Submission.CDT.LocationSing (sqP sqP_sub_sqP_le four_mul_add_one_le_sqP sqP_pos)

lemma gap_delta (P Q : ℕ) (hQ : 1 ≤ Q) (hPQ : Q < P)
    (hd : (P : ℝ) - (Q : ℝ) ≤ (Q : ℝ) * (1 / 10 ^ 6) * (1 + 2 / 10 ^ 6)) :
    (Submission.CDT.LocationSing.sqP (P : ℝ) - Submission.CDT.LocationSing.sqP (Q : ℝ)) /
      Submission.CDT.LocationSing.sqP (Q : ℝ) ≤ 1.0005 / 10 ^ 6 := by
  have hQpos : 0 < (Q : ℝ) := by
    have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := by linarith
  have hdnn : 0 ≤ (P : ℝ) - (Q : ℝ) := by
    have h : (Q : ℝ) < (P : ℝ) := by exact_mod_cast hPQ
    linarith
  have hBnn : 0 ≤ 2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1)) := by
    have h2 : 0 ≤ 2 + 1 / (2 * (Q : ℝ) + 1) := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) hdnn) h2
  have hsub := sqP_sub_sqP_le P Q hQ hPQ
  have hlow : 4 * (Q : ℝ) + 1 ≤ sqP (Q : ℝ) := four_mul_add_one_le_sqP _ hQ0
  have hsqPpos : 0 < sqP (Q : ℝ) := sqP_pos _ hQ0
  have h41 : (0 : ℝ) < 4 * (Q : ℝ) + 1 := by linarith
  -- replace the denominator `sqP Q` by the smaller `4Q + 1`
  have step1 : (sqP (P : ℝ) - sqP (Q : ℝ)) / sqP (Q : ℝ)
      ≤ (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) / (4 * (Q : ℝ) + 1) := by
    have a1 : (sqP (P : ℝ) - sqP (Q : ℝ)) / sqP (Q : ℝ)
        ≤ (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) / sqP (Q : ℝ) :=
      div_le_div_of_nonneg_right hsub (le_of_lt hsqPpos)
    have a2 : (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) / sqP (Q : ℝ)
        ≤ (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) / (4 * (Q : ℝ) + 1) :=
      div_le_div_of_nonneg_left hBnn h41 hlow
    linarith
  -- the elementary inequality `2(2 + 1/(2Q+1)) ≤ (4Q+1)/Q`
  have hkey : 2 * (2 + 1 / (2 * (Q : ℝ) + 1)) ≤ (4 * (Q : ℝ) + 1) / (Q : ℝ) := by
    rw [le_div_iff₀ hQpos]
    have h2q : (0 : ℝ) < 2 * (Q : ℝ) + 1 := by linarith
    field_simp
    nlinarith
  have step2 : (2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))) / (4 * (Q : ℝ) + 1)
      ≤ ((P : ℝ) - (Q : ℝ)) / (Q : ℝ) := by
    rw [div_le_iff₀ h41]
    calc 2 * ((P : ℝ) - (Q : ℝ)) * (2 + 1 / (2 * (Q : ℝ) + 1))
        = ((P : ℝ) - (Q : ℝ)) * (2 * (2 + 1 / (2 * (Q : ℝ) + 1))) := by ring
      _ ≤ ((P : ℝ) - (Q : ℝ)) * ((4 * (Q : ℝ) + 1) / (Q : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hdnn
      _ = (((P : ℝ) - (Q : ℝ)) / (Q : ℝ)) * (4 * (Q : ℝ) + 1) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
  have hnum : (1 / 10 ^ 6 : ℝ) * (1 + 2 / 10 ^ 6) ≤ 1.0005 / 10 ^ 6 := by norm_num
  have step3 : ((P : ℝ) - (Q : ℝ)) / (Q : ℝ) ≤ 1.0005 / 10 ^ 6 := by
    rw [div_le_iff₀ hQpos]
    have h1 := mul_le_mul_of_nonneg_right hnum (le_of_lt hQpos)
    nlinarith [hd, h1]
  linarith [step1, step2, step3]

end Work.CLoc
