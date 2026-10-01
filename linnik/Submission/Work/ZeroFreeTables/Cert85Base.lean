/-
# ZeroFreeTables — Cert85Base

The reduction lemmas for the Lemma 8.5 certificates of HB's Table 7
(`CertRow85`, `HBTable7_defs85`): they pass from the certificate condition,
in which `tfF` still occurs, to an explicit inequality in the atoms
`PhiS (c/λ)`, `PhiD (c/λ)`, … in which `norm_num` can evaluate everything except
`Real.pi` and the two exponentials `Real.exp (· * (π/2))`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs85
import Submission.Work.ZeroFreeTables.T7Cert

open scoped Real BigOperators
noncomputable section
namespace Work.ZeroFreeTables

/-- A Table 7 row with `b < c`, reduced to the strict failure of HB Lemma 8.5's
inequality written out with `PhiS`, `PhiD`. -/
lemma CertRow85_of_lt {b c l : ℝ} (hl : 0 < l) (hb0 : 0 ≤ b) (hbc : b < c)
    (h : 2 * PhiS (c/l)/PhiD (c/l) - 2 * PhiS ((c-b)/l)/PhiD ((c-b)/l)
          - (Real.pi/2 - 2)^2 + 2 * l * (Real.pi - 3) * ((3:ℝ)/8 + 4*0) < 0) :
    CertRow85 b c l 0 := by
  have hc : 0 < c := lt_of_le_of_lt hb0 hbc
  have hlne : l ≠ 0 := ne_of_gt hl
  have hm1 : c/l ≠ 0 := div_ne_zero (ne_of_gt hc) hlne
  have hcb : 0 < c - b := by linarith
  have hm2 : (c-b)/l ≠ 0 := div_ne_zero (ne_of_gt hcb) hlne
  unfold CertRow85
  refine ⟨hl, ?_⟩
  rw [show b - c = -(c-b) by ring, tfF_neg l c hlne (ne_of_gt hc),
      tfF_neg l (c-b) hlne (ne_of_gt hcb), tfF_zero, phiNeg_eq hm1, phiNeg_eq hm2]
  exact h

/-- The diagonal Table 7 row (`b = c`) for HB Lemma 8.5. -/
lemma CertRow85_of_eq {c l : ℝ} (hl : 0 < l) (hc : 0 < c)
    (h : 2 * PhiS (c/l)/PhiD (c/l) - 2 * (Real.pi/2 - 2)^2
          + 2 * l * (Real.pi - 3) * ((3:ℝ)/8 + 4*0) < 0) :
    CertRow85 c c l 0 := by
  have hlne : l ≠ 0 := ne_of_gt hl
  have hm1 : c/l ≠ 0 := div_ne_zero (ne_of_gt hc) hlne
  unfold CertRow85
  refine ⟨hl, ?_⟩
  rw [show c - c = (0:ℝ) by ring, tfF_neg l c hlne (ne_of_gt hc), tfF_zero, phiNeg_eq hm1]
  rw [show 2 * PhiS (c/l)/PhiD (c/l) - (Real.pi/2 - 2)^2 - (Real.pi/2 - 2)^2
        + (2 * l * (Real.pi - 3)) * ((3:ℝ)/8 + 4*0)
      = 2 * PhiS (c/l)/PhiD (c/l) - 2 * (Real.pi/2 - 2)^2
        + 2 * l * (Real.pi - 3) * ((3:ℝ)/8 + 4*0) by ring]
  exact h

end Work.ZeroFreeTables
