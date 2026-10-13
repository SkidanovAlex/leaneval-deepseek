import Mathlib
import Submission.Work.WilE7.LevelFibre.lfDefs

namespace Work.WilE7.LevelFibre

-- file: Submission/Work/WilE7/LevelFibre/lfE_lvIdx.lean, namespace Work.WilE7.LevelFibre,
-- imports Submission.Work.WilE7.LevelFibre.lfDefs
theorem lfE_lvIdx {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k)
    (hdim : lfD p q M k = (p + 1) + lfM p q M k) :
    lfE h j i hdim (lfLvIdx j i) = Fin.castAdd (lfM p q M k) (Fin.last p) := by
  apply Fin.ext
  show ((finEquiv hdim) (lfSwap h j i (lfLvIdx j i))).val = _
  rw [finEquiv_apply_val, lfSwap, Equiv.swap_apply_right]
  simp [Fin.val_castAdd, Fin.val_last]

end Work.WilE7.LevelFibre
