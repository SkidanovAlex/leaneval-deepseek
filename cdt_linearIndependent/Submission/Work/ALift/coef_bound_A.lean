import Mathlib
import Submission.Work.ALift.defs
import Submission.Work.Purge.a_side_clean

/-!
# Area ALift — the coefficient bound for `H = aH_A + bH_B + cH_C`

Under the absurd relation, `functionsH` (`Submission.CDT.functionsH_overconverges`) says that the
coefficient sequence of `H` overconverges to radius `1`: for every `r < 1` there is `C` with
`|h_n| ≤ C·r^{-n}`.  Taking `r = 10/11` gives the single bound `|h_n| ≤ C·(11/10)^n` used
throughout the continuation argument (the matching radius `10/11 > 9/10` is what makes the
initial disc `‖z‖ < 1/25` work).
-/

namespace Work.ALift

open Submission.CDTPlan

theorem coef_bound_A (a b c : ℤ) (hRel : ARel a b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖hcoef a b c k‖ ≤ C * (11 / 10 : ℝ) ^ k := by
  have hrel' : ((a : ℚ) : ℝ) + ((b : ℚ) : ℝ) * (Submission.CDT.L2chi3Real / 2)
      + ((c : ℚ) : ℝ) * (Submission.CDT.zeta2Real / 4) = 0 := by
    have := hRel; unfold ARel at this; push_cast; exact this
  have hclean := Work.Purge.a_side_clean
  have hB : Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffB :=
    hclean.2.2.2.2.2.2.1
  have hC : Submission.CDT.OverconvergesUnit Submission.CDT.eichlerDiffC :=
    hclean.2.2.2.2.2.2.2
  have hOC := Submission.CDT.functionsH_overconverges (a : ℚ) (b : ℚ) (c : ℚ) hrel' hB hC
  obtain ⟨C, hC0, hCb⟩ := hOC (10 / 11) (by norm_num) (by norm_num)
  refine ⟨C, le_of_lt hC0, fun k => ?_⟩
  have h1 : hcoef a b c k
      = ((Submission.CDT.ZagierH_coeff_seq (a : ℚ) (b : ℚ) (c : ℚ) k : ℚ) : ℂ) := by
    unfold hcoef Submission.CDTPlan.HZ Submission.CDT.ZagierH_coeff_seq
    rw [Submission.CDT.ZagierH_coeff]
  rw [h1, Complex.norm_ratCast]
  have h2 := hCb k
  rw [div_eq_mul_inv, div_pow, inv_div, ← div_pow] at h2
  exact h2

end Work.ALift
