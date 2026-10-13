import Mathlib
import Submission.Work.WilE7.LevelFibre.lfDefs

namespace Work.WilE7.LevelFibre

-- file: Submission/Work/WilE7/LevelFibre/lfE_xIdx.lean, namespace Work.WilE7.LevelFibre,
-- imports Submission.Work.WilE7.LevelFibre.lfDefs
theorem lfE_xIdx {p q M k : ℕ} (h : 1 ≤ (p + q) * k) (j : Fin q) (i : Fin k)
    (hdim : lfD p q M k = (p + 1) + lfM p q M k) (a : Fin p) :
    lfE h j i hdim (lfXIdx a) = Fin.castAdd (lfM p q M k) (Fin.castSucc a) := by
  -- The transposition `lfSwap h j i` fixes the base coordinates `lfXIdx a`.
  have hfix : lfSwap h j i (lfXIdx (q := q) (M := M) (k := k) a) =
      lfXIdx (q := q) (M := M) (k := k) a := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hc
      have hv := congrArg Fin.val hc
      simp only [lfXIdx_val] at hv
      have ha := a.isLt
      omega
    · intro hc
      have hv := congrArg Fin.val hc
      simp only [lfXIdx_val, lfLvIdx_val] at hv
      have ha := a.isLt
      omega
  -- and `finEquiv hdim` preserves values.
  have key : (lfE h j i hdim (lfXIdx (q := q) (M := M) (k := k) a)).val = a.val := by
    rw [lfE, Equiv.trans_apply, hfix]
    simp
  apply Fin.ext
  rw [key]
  simp

end Work.WilE7.LevelFibre
