import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Norm.strictMono_del_apply_eq

namespace Work.DSCOH.Struct

/-- If `y` is nondecreasing but not strictly increasing, then deleting the `b`-th entry for
`b ≥ frA y + 2` leaves a repeated value: the two positions `(frA y).castSucc` and
`(frA y).succ` of `y` carry the same value `frV y`, and both survive the deletion since they
lie strictly before `b`.  Hence `del y b` is not strictly increasing. -/
theorem mid_del_notStrictMono {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ)) :
    ¬ StrictMono (Work.DSCOH.Norm.del y b) := by
  intro hsm
  -- the two positions of the first repeat carry the same value ...
  have heq : y (Work.DSCOH.Norm.frA y hy hh).castSucc
      = y (Work.DSCOH.Norm.frA y hy hh).succ :=
    Work.DSCOH.Norm.firstRepeat_spec y hy hh
  -- ... and they are distinct.
  have hne : (Work.DSCOH.Norm.frA y hy hh).castSucc
      ≠ (Work.DSCOH.Norm.frA y hy hh).succ :=
    Fin.castSucc_lt_succ.ne
  -- A strictly increasing deletion must delete every repeated value: the deleted position is one
  -- of the two, contradicting `frA y + 2 ≤ b`.
  rcases Work.DSCOH.Norm.strictMono_del_apply_eq hsm hne heq with h | h
  · have hb : (b : ℕ) = (Work.DSCOH.Norm.frA y hy hh : ℕ) := by
      rw [h, Fin.val_castSucc]
    omega
  · have hb : (b : ℕ) = (Work.DSCOH.Norm.frA y hy hh : ℕ) + 1 := by
      rw [h, Fin.val_succ]
    omega

end Work.DSCOH.Struct
