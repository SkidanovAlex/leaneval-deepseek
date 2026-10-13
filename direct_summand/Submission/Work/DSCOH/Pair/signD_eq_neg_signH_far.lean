import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Struct.readD_mid
import Submission.Work.DSCOH.Struct.readD_gt
import Submission.Work.DSCOH.Struct.mid_firstRepeat_del
import Submission.Work.DSCOH.Struct.firstRepeat_del_gt

namespace Work.DSCOH.Pair

theorem signD_eq_neg_signH_far {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ)) :
    Work.DSCOH.Norm.signD y hy hh b = - Work.DSCOH.Norm.signH y hy hh b.succ := by
  -- `signD y b` equals `(-1)^(frA y + b)` in both the middle and the far case.
  have hD : Work.DSCOH.Norm.signD y hy hh b
      = (-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) := by
    rcases lt_or_ge (Work.DSCOH.Norm.frA2 y hy hh : ℕ) (b : ℕ) with h | h
    · rw [(Work.DSCOH.Struct.readD_gt y hy hh b h).2]
      have hsv : (b.succ : ℕ) = (b : ℕ) + 1 := Fin.val_succ b
      rw [hsv, show (Work.DSCOH.Norm.frA y hy hh : ℕ) + ((b : ℕ) + 1)
            = ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) + 1 by omega, pow_succ]
      ring
    · exact (Work.DSCOH.Struct.readD_mid y hy hh b hb h).2
  have hH : Work.DSCOH.Norm.signH y hy hh b.succ
      = -(-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) := by
    rw [Work.DSCOH.Norm.signH]
    have hsv : (b.succ : ℕ) = (b : ℕ) + 1 := Fin.val_succ b
    rw [hsv, show (Work.DSCOH.Norm.frA y hy hh : ℕ) + ((b : ℕ) + 1)
          = ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) + 1 by omega, pow_succ]
    ring
  rw [hD, hH, neg_neg]

end Work.DSCOH.Pair
