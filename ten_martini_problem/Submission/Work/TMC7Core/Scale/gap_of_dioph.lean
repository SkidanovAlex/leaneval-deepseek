import Mathlib
import Submission.Work.TMC7Core.Defs

namespace Work.TMC7Core.Scale

set_option linter.unusedVariables false in
/-- If `α` admits an eventual Diophantine lower bound `fracDist (kα) ≥ exp(-b k)`
(`DiophBelow α b`) and is well approximated by the rationals `A m / N m` with error
`≤ 1/(N m · N (m+1))`, then the denominators `N m` cannot grow faster than
`exp (b · N m)` eventually.

Indeed, `|N m · α - A m| ≤ 1/N (m+1)` shows `fracDist (N m · α) ≤ 1/N (m+1)`, while
`DiophBelow` applied at `k = N m` gives `exp(-b · N m) ≤ fracDist (N m · α)`. -/
theorem gap_of_dioph (α b : ℝ) (hb : 0 < b) (N : ℕ → ℕ) (A : ℕ → ℤ)
    (hN1 : ∀ m, 1 ≤ N m) (hmono : StrictMono N)
    (hbd : ∀ m, |α - (A m : ℝ) / (N m : ℝ)| ≤ 1 / ((N m : ℝ) * (N (m + 1) : ℝ)))
    (hD : Work.TMC7Core.DiophBelow α b) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (N (m + 1) : ℝ) ≤ Real.exp (b * (N m : ℝ)) := by
  rw [Work.TMC7Core.DiophBelow, Filter.eventually_atTop] at hD
  obtain ⟨K, hK⟩ := hD
  refine ⟨K, fun m hm => ?_⟩
  have hNK : K ≤ N m := le_trans hm (hmono.id_le m)
  have hstep := hK (N m) hNK
  have hNm_pos : (0 : ℝ) < (N m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (hN1 m)
  have hNm1_pos : (0 : ℝ) < (N (m + 1) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (hN1 (m + 1))
  have hNm_ne : (N m : ℝ) ≠ 0 := ne_of_gt hNm_pos
  have hNm1_ne : (N (m + 1) : ℝ) ≠ 0 := ne_of_gt hNm1_pos
  -- `|N m · α - A m| = N m · |α - A m / N m|`
  have hfac : |(N m : ℝ) * α - (A m : ℝ)| =
      (N m : ℝ) * |α - (A m : ℝ) / (N m : ℝ)| := by
    have hc : (N m : ℝ) * ((A m : ℝ) / (N m : ℝ)) = (A m : ℝ) := by field_simp
    rw [show (N m : ℝ) * α - (A m : ℝ) =
        (N m : ℝ) * (α - (A m : ℝ) / (N m : ℝ)) by rw [mul_sub, hc]]
    rw [abs_mul, abs_of_pos hNm_pos]
  -- `fracDist (N m · α) ≤ 1 / N (m+1)`
  have hle1 : Work.TMC7Core.fracDist ((N m : ℝ) * α) ≤ 1 / (N (m + 1) : ℝ) := by
    have h1 : Work.TMC7Core.fracDist ((N m : ℝ) * α) ≤ |(N m : ℝ) * α - (A m : ℝ)| := by
      rw [Work.TMC7Core.fracDist]
      exact round_le _ (A m)
    refine le_trans h1 ?_
    rw [hfac]
    calc (N m : ℝ) * |α - (A m : ℝ) / (N m : ℝ)|
        ≤ (N m : ℝ) * (1 / ((N m : ℝ) * (N (m + 1) : ℝ))) :=
          mul_le_mul_of_nonneg_left (hbd m) (le_of_lt hNm_pos)
      _ = 1 / (N (m + 1) : ℝ) := by field_simp
  have hkey : (Real.exp (b * (N m : ℝ)))⁻¹ ≤ (N (m + 1) : ℝ)⁻¹ := by
    have h := le_trans hstep hle1
    simpa [Real.exp_neg, one_div] using h
  exact (inv_le_inv₀ (Real.exp_pos _) hNm1_pos).mp hkey

end Work.TMC7Core.Scale
