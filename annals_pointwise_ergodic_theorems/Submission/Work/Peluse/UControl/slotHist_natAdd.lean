import Mathlib
import Submission.Work.Peluse.UControl.levRoundDefs

namespace Work.Peluse.UControl

theorem slotHist_natAdd {L r : ℕ} (h₀ : Fin L → Bool) (w : Fin r → Bool) (j : Fin r) :
    slotHist h₀ r w (Fin.natAdd L j) = w j := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    rw [slotHist]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [Fin.natAdd_castSucc, Fin.snoc_castSucc]
      exact ih (Fin.init w) k
    · rw [Fin.natAdd_last]
      exact Fin.snoc_last (α := fun _ => Bool) (w (Fin.last r)) (slotHist h₀ r (Fin.init w))

end Work.Peluse.UControl
