import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Struct.readD_mid
import Submission.Work.DSCOH.Struct.readD_gt
import Submission.Work.DSCOH.Struct.readH_eq
import Submission.Work.DSCOH.Struct.mid_del_notStrictMono
import Submission.Work.DSCOH.Struct.del_not_strictMono_gt
import Submission.Work.DSCOH.Struct.mid_firstRepeat_del
import Submission.Work.DSCOH.Struct.firstRepeat_del_gt

namespace Work.DSCOH.Pair

theorem readD_readH_far {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ)) :
    ¬ StrictMono (Work.DSCOH.Norm.del y b) ∧
      Work.DSCOH.Norm.readD y hy hh b = Work.DSCOH.Norm.readH y hy hh b.succ := by
  -- `b ≥ frA y + 2` forces `b` to be past both positions of the first repeat, so deleting `b`
  -- cannot remove the repeat: `del y b` is not strictly increasing.
  have hns : ¬ StrictMono (Work.DSCOH.Norm.del y b) :=
    Work.DSCOH.Struct.mid_del_notStrictMono y hy hh b hb
  refine ⟨hns, ?_⟩
  -- Split according to whether `b` still lies inside the block of entries equal to `frV y`
  -- (middle case) or strictly past it (`frA2 y < b`, the "far" case).
  by_cases hmid : (b : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ)
  · -- Middle case: both read indices reconstruct `y` itself.
    have hD : Work.DSCOH.Norm.readD y hy hh b = y :=
      (Work.DSCOH.Struct.readD_mid y hy hh b hb hmid).1
    have hH : Work.DSCOH.Norm.readH y hy hh b.succ = y :=
      Work.DSCOH.Struct.readH_eq y hy hh b.succ
        (by have := Fin.val_succ b; omega)
        (by have := Fin.val_succ b; omega)
    rw [hD, hH]
  · -- Far case: both read indices are the deletion of the `(b+1)`-st entry of the duplication
    -- of the first repeat of `y`.
    have hgt : (Work.DSCOH.Norm.frA2 y hy hh : ℕ) < (b : ℕ) := not_le.mp hmid
    have hD : Work.DSCOH.Norm.readD y hy hh b =
        Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y (Work.DSCOH.Norm.frA y hy hh).castSucc)
          b.succ :=
      (Work.DSCOH.Struct.readD_gt y hy hh b hgt).1
    rw [hD]
    rfl

end Work.DSCOH.Pair
