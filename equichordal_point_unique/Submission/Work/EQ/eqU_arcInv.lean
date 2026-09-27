import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_gamma

namespace Work.EQ

open Complex

/-- **`arcInv` is a right inverse of `eqU`.**  For `O₂ = a/2`, any `z` at distance `< 1`
from `O₁ = -O₂` (i.e. `‖z + a/2‖ < 1`) satisfies `eqU a (arcInv a z) = z`, where
`arcInv a z = O₂ + (1 - ‖z + O₂‖) * (z + O₂)/‖z + O₂‖` (`Submission.Work.EQ.hetero_gamma`).

Pure algebra.  Write `w = z + O₂` (`= z - O₁`) and `s = ‖w‖`; then
`arcInv a z - O₂ = (1-s) * ↑(w / s)` and `‖arcInv a z - O₂‖ = |1-s| = 1-s` (because `s < 1`), so
`eqU a (arcInv a z) = -O₂ + ↑(1-s) * ↑(w/s) * (1/↑(1-s)) = -O₂ + ↑w = z`
using `eqU a P = -P + (P - O₂)/‖P - O₂‖` and `‖P - O₂‖ = 1 - s` at `P = arcInv a z`.
The degenerate case `w = 0` (i.e. `z = -O₂`) is included: by the convention `x / 0 = 0` in `ℂ`,
`arcInv a (-O₂) = O₂` and `eqU a O₂ = -O₂`, so the identity still holds; handle it separately
or make the algebra robust to it.  Useful: `norm_ofReal_eq` and `Complex.ofReal_div`,
`Complex.ofReal_sub`, `abs_of_pos`, `field_simp`, `ring`. -/
theorem eqU_arcInv (a : ℝ) {z : ℂ} (hz : ‖z + (((a / 2 : ℝ)) : ℂ)‖ < 1) :
    eqU a (arcInv a z) = z := by
  rcases eq_or_ne (z + ((a / 2 : ℝ) : ℂ)) 0 with hw0 | hwne
  · -- Degenerate case `z = -O₂`: `arcInv a z = O₂` and `eqU a O₂ = -O₂`.
    have hz_eq : z = -(((a / 2 : ℝ)) : ℂ) := eq_neg_of_add_eq_zero_left hw0
    have hP : arcInv a z = (((a / 2 : ℝ)) : ℂ) := by
      simp only [arcInv]
      rw [hw0]
      simp
    rw [hP, hz_eq]
    simp only [eqU]
    simp
  · -- Non-degenerate case: `w = z + O₂ ≠ 0`.
    set b : ℂ := ((a / 2 : ℝ) : ℂ) with hb
    set w : ℂ := z + b with hw
    set s : ℝ := ‖w‖ with hs
    have hz1 : s < 1 := by rw [hs]; exact hz
    have hspos : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hwne
    have hsnn : 0 ≤ s := hspos.le
    have hsne : ((s : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact hspos.ne'
    have h1spos : 0 < 1 - s := by linarith
    have h1sne : (((1 - s : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact h1spos.ne'
    set P : ℂ := arcInv a z with hP
    -- `P - O₂ = (1 - s) * (w / ‖w‖)`
    have hPsub : P - b = ((1 - s : ℝ) : ℂ) * (w / ((s : ℝ) : ℂ)) := by
      rw [hP]
      simp only [arcInv]
      rw [← hb, ← hw, ← hs]
      rw [Complex.ofReal_sub, Complex.ofReal_one]
      exact add_sub_cancel_left b _
    -- `‖P - O₂‖ = 1 - s`
    have hPr : ‖P - b‖ = 1 - s := by
      rw [hPsub, norm_mul, norm_div, Work.EQ.norm_ofReal_eq, abs_of_pos h1spos,
        ← hs, Work.EQ.norm_ofReal_eq, abs_of_nonneg hsnn, div_self hspos.ne', mul_one]
    have hPne : P - b ≠ 0 := by
      rw [hPsub]
      exact mul_ne_zero h1sne (div_ne_zero hwne hsne)
    -- `eqU a P + O₂ = w`
    have hkey : eqU a P + b = w := by
      rw [eqU_add_eqU a P hPne, hPr, hPsub]
      have hval : ((1 - (1 - s)) / (1 - s) : ℝ) = s / (1 - s) := by
        rw [show (1 : ℝ) - (1 - s) = s by ring]
      rw [hval, Complex.ofReal_div]
      rw [show ((s : ℂ) / ((1 - s : ℝ) : ℂ)) * (((1 - s : ℝ) : ℂ) * (w / (s : ℂ)))
            = w from by
        rw [← mul_assoc, div_mul_cancel₀ _ h1sne, mul_div_cancel₀ _ hsne]]
    exact eq_sub_of_add_eq hkey ▸ (by rw [hw]; ring)

end Work.EQ
