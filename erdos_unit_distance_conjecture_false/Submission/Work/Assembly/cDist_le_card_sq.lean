import Mathlib
import Submission.Work.Defs.Basic

namespace Work.Assembly

theorem cDist_le_card_sq (P : Finset ℂ) :
    (Work.Defs.cDist P : ℝ) ≤ (P.card : ℝ) ^ 2 := by
  have h : Work.Defs.cDist P ≤ P.card ^ 2 := by
    calc Work.Defs.cDist P
        ≤ (P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1)).card := Nat.div_le_self _ _
      _ ≤ P.offDiag.card := Finset.card_filter_le _ _
      _ = P.card * P.card - P.card := Finset.offDiag_card P
      _ ≤ P.card ^ 2 := by rw [pow_two]; exact Nat.sub_le _ _
  exact_mod_cast h

end Work.Assembly
