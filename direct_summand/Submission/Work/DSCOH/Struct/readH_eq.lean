import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Struct.frV_eq_of_between
import Submission.Work.DSCOH.Struct.del_dup_eq_self

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-- `readH y c` (duplicate the first repeat of `y`, then delete position `c`) is `y` again, for
every deletion position `c` ranging from the first repeat to one past the last occurrence of the
repeated value.

Indeed `dup y (frA y).castSucc` is `y` with a copy of `y (frA y)` inserted after that position, so
its entries at the positions `frA y, …, frA2 y + 1` all carry the value `frV y` (the inserted copy
at position `frA y + 1` duplicates the entry at `frA y`, and `y` is constantly `frV y` on
`[frA y, frA2 y]`).  Deleting any one of them therefore leaves the tuple `y` unchanged. -/
theorem readH_eq {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (c : Fin (k + 3))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ (c : ℕ))
    (h2 : (c : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) + 1) :
    Work.DSCOH.Norm.readH y hy hh c = y := by
  show Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y (Work.DSCOH.Norm.frA y hy hh).castSucc) c = y
  refine del_dup_eq_self (L := k + 1) y (Work.DSCOH.Norm.frA y hy hh).castSucc
    ((Work.DSCOH.Norm.frA2 y hy hh : ℕ) + 1) ?_ c h1 h2
  intro i hi1 hi2
  -- `y` is constantly `frV y` on the block `[frA y, frA2 y]`
  have hir : (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ (i : ℕ) := by simpa using hi1
  have hF : (i : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) := by omega
  have hA₁ : (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ ((i.castSucc : Fin (k + 2)) : ℕ) := by
    simpa only [Fin.val_castSucc] using hir
  have hB₁ : ((i.castSucc : Fin (k + 2)) : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) := by
    simpa only [Fin.val_castSucc] using hF
  have hA₂ : (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ ((i.succ : Fin (k + 2)) : ℕ) := by
    simpa only [Fin.val_succ] using
      (show (Work.DSCOH.Norm.frA y hy hh : ℕ) ≤ (i : ℕ) + 1 from by omega)
  have hB₂ : ((i.succ : Fin (k + 2)) : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) := by
    simpa only [Fin.val_succ] using
      (show (i : ℕ) + 1 ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) from by omega)
  rw [frV_eq_of_between y hy hh i.castSucc hA₁ hB₁,
    frV_eq_of_between y hy hh i.succ hA₂ hB₂]

end Work.DSCOH.Struct
