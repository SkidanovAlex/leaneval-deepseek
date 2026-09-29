import Submission.Work.CNum.CertC.EqA
import Submission.Work.CNum.CertC.DnA
import Submission.Work.CNum.CertC.EqB
import Submission.Work.CNum.CertC.DnB
import Submission.Work.CNum.CertC.EqC
import Submission.Work.CNum.CertC.DnC
import Submission.Work.CNum.CertC.EqD
import Submission.Work.CNum.CertC.DnD
import Submission.Work.CNum.CertC.EqE
import Submission.Work.CNum.CertC.DnE
import Submission.Work.CNum.CertC.EqF
import Submission.Work.CNum.CertC.DnF
import Submission.Work.CNum.CertC.EqG
import Submission.Work.CNum.CertC.DnG
import Submission.Work.CNum.CertC.EqH
import Submission.Work.CNum.CertC.DnH
/-!
# `Work.CNum.CertC.Bnd` — the per-arc certificate `bnd_k` (cheap route)

For each `k < 1024`, `Gv k` equals the tabulated literal (`Gv_eq_T` + the chunk modules) and
`LOG1E13LB ≤ gv k` (`gv_eq_T` + the chunk modules).  This is a drop-in replacement for the
`bnd_k` of `Work.CNum.CertB.{A..H}`, with the kernel evaluations confined to the cheap
`GvT`/`gvT` (tabulated) expressions.
-/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem bnd_0 : Gv 0 = -30832514568 ∧ LOG1E13LB ≤ gv 0 := by
  constructor
  · rw [Gv_eq_T 0 (by norm_num)]
    exact EqAv 0 (by norm_num)
  · rw [gv_eq_T 0 (by norm_num)]
    exact DnAv 0 (by norm_num)

theorem bnd_1 : Gv 1 = -30756339654 ∧ LOG1E13LB ≤ gv 1 := by
  constructor
  · rw [Gv_eq_T 1 (by norm_num)]
    exact EqAv 1 (by norm_num)
  · rw [gv_eq_T 1 (by norm_num)]
    exact DnAv 1 (by norm_num)

theorem bnd_2 : Gv 2 = -30630076488 ∧ LOG1E13LB ≤ gv 2 := by
  constructor
  · rw [Gv_eq_T 2 (by norm_num)]
    exact EqAv 2 (by norm_num)
  · rw [gv_eq_T 2 (by norm_num)]
    exact DnAv 2 (by norm_num)

theorem bnd_3 : Gv 3 = -30454747574 ∧ LOG1E13LB ≤ gv 3 := by
  constructor
  · rw [Gv_eq_T 3 (by norm_num)]
    exact EqAv 3 (by norm_num)
  · rw [gv_eq_T 3 (by norm_num)]
    exact DnAv 3 (by norm_num)

theorem bnd_4 : Gv 4 = -30231776270 ∧ LOG1E13LB ≤ gv 4 := by
  constructor
  · rw [Gv_eq_T 4 (by norm_num)]
    exact EqAv 4 (by norm_num)
  · rw [gv_eq_T 4 (by norm_num)]
    exact DnAv 4 (by norm_num)

theorem bnd_5 : Gv 5 = -29962918678 ∧ LOG1E13LB ≤ gv 5 := by
  constructor
  · rw [Gv_eq_T 5 (by norm_num)]
    exact EqAv 5 (by norm_num)
  · rw [gv_eq_T 5 (by norm_num)]
    exact DnAv 5 (by norm_num)

theorem bnd_6 : Gv 6 = -29650262318 ∧ LOG1E13LB ≤ gv 6 := by
  constructor
  · rw [Gv_eq_T 6 (by norm_num)]
    exact EqAv 6 (by norm_num)
  · rw [gv_eq_T 6 (by norm_num)]
    exact DnAv 6 (by norm_num)

theorem bnd_7 : Gv 7 = -29296171070 ∧ LOG1E13LB ≤ gv 7 := by
  constructor
  · rw [Gv_eq_T 7 (by norm_num)]
    exact EqAv 7 (by norm_num)
  · rw [gv_eq_T 7 (by norm_num)]
    exact DnAv 7 (by norm_num)

theorem bnd_8 : Gv 8 = -28903238126 ∧ LOG1E13LB ≤ gv 8 := by
  constructor
  · rw [Gv_eq_T 8 (by norm_num)]
    exact EqAv 8 (by norm_num)
  · rw [gv_eq_T 8 (by norm_num)]
    exact DnAv 8 (by norm_num)

theorem bnd_9 : Gv 9 = -28474297176 ∧ LOG1E13LB ≤ gv 9 := by
  constructor
  · rw [Gv_eq_T 9 (by norm_num)]
    exact EqAv 9 (by norm_num)
  · rw [gv_eq_T 9 (by norm_num)]
    exact DnAv 9 (by norm_num)

theorem bnd_10 : Gv 10 = -28012245494 ∧ LOG1E13LB ≤ gv 10 := by
  constructor
  · rw [Gv_eq_T 10 (by norm_num)]
    exact EqAv 10 (by norm_num)
  · rw [gv_eq_T 10 (by norm_num)]
    exact DnAv 10 (by norm_num)

theorem bnd_11 : Gv 11 = -27520179758 ∧ LOG1E13LB ≤ gv 11 := by
  constructor
  · rw [Gv_eq_T 11 (by norm_num)]
    exact EqAv 11 (by norm_num)
  · rw [gv_eq_T 11 (by norm_num)]
    exact DnAv 11 (by norm_num)

theorem bnd_12 : Gv 12 = -27001164088 ∧ LOG1E13LB ≤ gv 12 := by
  constructor
  · rw [Gv_eq_T 12 (by norm_num)]
    exact EqAv 12 (by norm_num)
  · rw [gv_eq_T 12 (by norm_num)]
    exact DnAv 12 (by norm_num)

theorem bnd_13 : Gv 13 = -26458333254 ∧ LOG1E13LB ≤ gv 13 := by
  constructor
  · rw [Gv_eq_T 13 (by norm_num)]
    exact EqAv 13 (by norm_num)
  · rw [gv_eq_T 13 (by norm_num)]
    exact DnAv 13 (by norm_num)

theorem bnd_14 : Gv 14 = -25894784088 ∧ LOG1E13LB ≤ gv 14 := by
  constructor
  · rw [Gv_eq_T 14 (by norm_num)]
    exact EqAv 14 (by norm_num)
  · rw [gv_eq_T 14 (by norm_num)]
    exact DnAv 14 (by norm_num)

theorem bnd_15 : Gv 15 = -25313555208 ∧ LOG1E13LB ≤ gv 15 := by
  constructor
  · rw [Gv_eq_T 15 (by norm_num)]
    exact EqAv 15 (by norm_num)
  · rw [gv_eq_T 15 (by norm_num)]
    exact DnAv 15 (by norm_num)

theorem bnd_16 : Gv 16 = -24717586564 ∧ LOG1E13LB ≤ gv 16 := by
  constructor
  · rw [Gv_eq_T 16 (by norm_num)]
    exact EqAv 16 (by norm_num)
  · rw [gv_eq_T 16 (by norm_num)]
    exact DnAv 16 (by norm_num)

theorem bnd_17 : Gv 17 = -24109741548 ∧ LOG1E13LB ≤ gv 17 := by
  constructor
  · rw [Gv_eq_T 17 (by norm_num)]
    exact EqAv 17 (by norm_num)
  · rw [gv_eq_T 17 (by norm_num)]
    exact DnAv 17 (by norm_num)

theorem bnd_18 : Gv 18 = -23492720104 ∧ LOG1E13LB ≤ gv 18 := by
  constructor
  · rw [Gv_eq_T 18 (by norm_num)]
    exact EqAv 18 (by norm_num)
  · rw [gv_eq_T 18 (by norm_num)]
    exact DnAv 18 (by norm_num)

theorem bnd_19 : Gv 19 = -22869041388 ∧ LOG1E13LB ≤ gv 19 := by
  constructor
  · rw [Gv_eq_T 19 (by norm_num)]
    exact EqAv 19 (by norm_num)
  · rw [gv_eq_T 19 (by norm_num)]
    exact DnAv 19 (by norm_num)

theorem bnd_20 : Gv 20 = -22241142096 ∧ LOG1E13LB ≤ gv 20 := by
  constructor
  · rw [Gv_eq_T 20 (by norm_num)]
    exact EqAv 20 (by norm_num)
  · rw [gv_eq_T 20 (by norm_num)]
    exact DnAv 20 (by norm_num)

theorem bnd_21 : Gv 21 = -21611192266 ∧ LOG1E13LB ≤ gv 21 := by
  constructor
  · rw [Gv_eq_T 21 (by norm_num)]
    exact EqAv 21 (by norm_num)
  · rw [gv_eq_T 21 (by norm_num)]
    exact DnAv 21 (by norm_num)

theorem bnd_22 : Gv 22 = -20981275646 ∧ LOG1E13LB ≤ gv 22 := by
  constructor
  · rw [Gv_eq_T 22 (by norm_num)]
    exact EqAv 22 (by norm_num)
  · rw [gv_eq_T 22 (by norm_num)]
    exact DnAv 22 (by norm_num)

theorem bnd_23 : Gv 23 = -20353214580 ∧ LOG1E13LB ≤ gv 23 := by
  constructor
  · rw [Gv_eq_T 23 (by norm_num)]
    exact EqAv 23 (by norm_num)
  · rw [gv_eq_T 23 (by norm_num)]
    exact DnAv 23 (by norm_num)

theorem bnd_24 : Gv 24 = -19728727324 ∧ LOG1E13LB ≤ gv 24 := by
  constructor
  · rw [Gv_eq_T 24 (by norm_num)]
    exact EqAv 24 (by norm_num)
  · rw [gv_eq_T 24 (by norm_num)]
    exact DnAv 24 (by norm_num)

theorem bnd_25 : Gv 25 = -19109316164 ∧ LOG1E13LB ≤ gv 25 := by
  constructor
  · rw [Gv_eq_T 25 (by norm_num)]
    exact EqAv 25 (by norm_num)
  · rw [gv_eq_T 25 (by norm_num)]
    exact DnAv 25 (by norm_num)

theorem bnd_26 : Gv 26 = -18496342248 ∧ LOG1E13LB ≤ gv 26 := by
  constructor
  · rw [Gv_eq_T 26 (by norm_num)]
    exact EqAv 26 (by norm_num)
  · rw [gv_eq_T 26 (by norm_num)]
    exact DnAv 26 (by norm_num)

theorem bnd_27 : Gv 27 = -17890959316 ∧ LOG1E13LB ≤ gv 27 := by
  constructor
  · rw [Gv_eq_T 27 (by norm_num)]
    exact EqAv 27 (by norm_num)
  · rw [gv_eq_T 27 (by norm_num)]
    exact DnAv 27 (by norm_num)

theorem bnd_28 : Gv 28 = -17294234722 ∧ LOG1E13LB ≤ gv 28 := by
  constructor
  · rw [Gv_eq_T 28 (by norm_num)]
    exact EqAv 28 (by norm_num)
  · rw [gv_eq_T 28 (by norm_num)]
    exact DnAv 28 (by norm_num)

theorem bnd_29 : Gv 29 = -16707053940 ∧ LOG1E13LB ≤ gv 29 := by
  constructor
  · rw [Gv_eq_T 29 (by norm_num)]
    exact EqAv 29 (by norm_num)
  · rw [gv_eq_T 29 (by norm_num)]
    exact DnAv 29 (by norm_num)

theorem bnd_30 : Gv 30 = -16130170572 ∧ LOG1E13LB ≤ gv 30 := by
  constructor
  · rw [Gv_eq_T 30 (by norm_num)]
    exact EqAv 30 (by norm_num)
  · rw [gv_eq_T 30 (by norm_num)]
    exact DnAv 30 (by norm_num)

theorem bnd_31 : Gv 31 = -15564240076 ∧ LOG1E13LB ≤ gv 31 := by
  constructor
  · rw [Gv_eq_T 31 (by norm_num)]
    exact EqAv 31 (by norm_num)
  · rw [gv_eq_T 31 (by norm_num)]
    exact DnAv 31 (by norm_num)

theorem bnd_32 : Gv 32 = -15009780550 ∧ LOG1E13LB ≤ gv 32 := by
  constructor
  · rw [Gv_eq_T 32 (by norm_num)]
    exact EqAv 32 (by norm_num)
  · rw [gv_eq_T 32 (by norm_num)]
    exact DnAv 32 (by norm_num)

theorem bnd_33 : Gv 33 = -14467182980 ∧ LOG1E13LB ≤ gv 33 := by
  constructor
  · rw [Gv_eq_T 33 (by norm_num)]
    exact EqAv 33 (by norm_num)
  · rw [gv_eq_T 33 (by norm_num)]
    exact DnAv 33 (by norm_num)

theorem bnd_34 : Gv 34 = -13936804782 ∧ LOG1E13LB ≤ gv 34 := by
  constructor
  · rw [Gv_eq_T 34 (by norm_num)]
    exact EqAv 34 (by norm_num)
  · rw [gv_eq_T 34 (by norm_num)]
    exact DnAv 34 (by norm_num)

theorem bnd_35 : Gv 35 = -13418876104 ∧ LOG1E13LB ≤ gv 35 := by
  constructor
  · rw [Gv_eq_T 35 (by norm_num)]
    exact EqAv 35 (by norm_num)
  · rw [gv_eq_T 35 (by norm_num)]
    exact DnAv 35 (by norm_num)

theorem bnd_36 : Gv 36 = -12913559494 ∧ LOG1E13LB ≤ gv 36 := by
  constructor
  · rw [Gv_eq_T 36 (by norm_num)]
    exact EqAv 36 (by norm_num)
  · rw [gv_eq_T 36 (by norm_num)]
    exact DnAv 36 (by norm_num)

theorem bnd_37 : Gv 37 = -12420948498 ∧ LOG1E13LB ≤ gv 37 := by
  constructor
  · rw [Gv_eq_T 37 (by norm_num)]
    exact EqAv 37 (by norm_num)
  · rw [gv_eq_T 37 (by norm_num)]
    exact DnAv 37 (by norm_num)

theorem bnd_38 : Gv 38 = -11941069718 ∧ LOG1E13LB ≤ gv 38 := by
  constructor
  · rw [Gv_eq_T 38 (by norm_num)]
    exact EqAv 38 (by norm_num)
  · rw [gv_eq_T 38 (by norm_num)]
    exact DnAv 38 (by norm_num)

theorem bnd_39 : Gv 39 = -11473905460 ∧ LOG1E13LB ≤ gv 39 := by
  constructor
  · rw [Gv_eq_T 39 (by norm_num)]
    exact EqAv 39 (by norm_num)
  · rw [gv_eq_T 39 (by norm_num)]
    exact DnAv 39 (by norm_num)

theorem bnd_40 : Gv 40 = -11019392984 ∧ LOG1E13LB ≤ gv 40 := by
  constructor
  · rw [Gv_eq_T 40 (by norm_num)]
    exact EqAv 40 (by norm_num)
  · rw [gv_eq_T 40 (by norm_num)]
    exact DnAv 40 (by norm_num)

theorem bnd_41 : Gv 41 = -10577427186 ∧ LOG1E13LB ≤ gv 41 := by
  constructor
  · rw [Gv_eq_T 41 (by norm_num)]
    exact EqAv 41 (by norm_num)
  · rw [gv_eq_T 41 (by norm_num)]
    exact DnAv 41 (by norm_num)

theorem bnd_42 : Gv 42 = -10147841792 ∧ LOG1E13LB ≤ gv 42 := by
  constructor
  · rw [Gv_eq_T 42 (by norm_num)]
    exact EqAv 42 (by norm_num)
  · rw [gv_eq_T 42 (by norm_num)]
    exact DnAv 42 (by norm_num)

theorem bnd_43 : Gv 43 = -9730483980 ∧ LOG1E13LB ≤ gv 43 := by
  constructor
  · rw [Gv_eq_T 43 (by norm_num)]
    exact EqAv 43 (by norm_num)
  · rw [gv_eq_T 43 (by norm_num)]
    exact DnAv 43 (by norm_num)

theorem bnd_44 : Gv 44 = -9325145800 ∧ LOG1E13LB ≤ gv 44 := by
  constructor
  · rw [Gv_eq_T 44 (by norm_num)]
    exact EqAv 44 (by norm_num)
  · rw [gv_eq_T 44 (by norm_num)]
    exact DnAv 44 (by norm_num)

theorem bnd_45 : Gv 45 = -8931612564 ∧ LOG1E13LB ≤ gv 45 := by
  constructor
  · rw [Gv_eq_T 45 (by norm_num)]
    exact EqAv 45 (by norm_num)
  · rw [gv_eq_T 45 (by norm_num)]
    exact DnAv 45 (by norm_num)

theorem bnd_46 : Gv 46 = -8549634324 ∧ LOG1E13LB ≤ gv 46 := by
  constructor
  · rw [Gv_eq_T 46 (by norm_num)]
    exact EqAv 46 (by norm_num)
  · rw [gv_eq_T 46 (by norm_num)]
    exact DnAv 46 (by norm_num)

theorem bnd_47 : Gv 47 = -8178974204 ∧ LOG1E13LB ≤ gv 47 := by
  constructor
  · rw [Gv_eq_T 47 (by norm_num)]
    exact EqAv 47 (by norm_num)
  · rw [gv_eq_T 47 (by norm_num)]
    exact DnAv 47 (by norm_num)

theorem bnd_48 : Gv 48 = -7819363524 ∧ LOG1E13LB ≤ gv 48 := by
  constructor
  · rw [Gv_eq_T 48 (by norm_num)]
    exact EqAv 48 (by norm_num)
  · rw [gv_eq_T 48 (by norm_num)]
    exact DnAv 48 (by norm_num)

theorem bnd_49 : Gv 49 = -7470524744 ∧ LOG1E13LB ≤ gv 49 := by
  constructor
  · rw [Gv_eq_T 49 (by norm_num)]
    exact EqAv 49 (by norm_num)
  · rw [gv_eq_T 49 (by norm_num)]
    exact DnAv 49 (by norm_num)

theorem bnd_50 : Gv 50 = -7132211344 ∧ LOG1E13LB ≤ gv 50 := by
  constructor
  · rw [Gv_eq_T 50 (by norm_num)]
    exact EqAv 50 (by norm_num)
  · rw [gv_eq_T 50 (by norm_num)]
    exact DnAv 50 (by norm_num)

theorem bnd_51 : Gv 51 = -6804111178 ∧ LOG1E13LB ≤ gv 51 := by
  constructor
  · rw [Gv_eq_T 51 (by norm_num)]
    exact EqAv 51 (by norm_num)
  · rw [gv_eq_T 51 (by norm_num)]
    exact DnAv 51 (by norm_num)

theorem bnd_52 : Gv 52 = -6485943008 ∧ LOG1E13LB ≤ gv 52 := by
  constructor
  · rw [Gv_eq_T 52 (by norm_num)]
    exact EqAv 52 (by norm_num)
  · rw [gv_eq_T 52 (by norm_num)]
    exact DnAv 52 (by norm_num)

theorem bnd_53 : Gv 53 = -6177452800 ∧ LOG1E13LB ≤ gv 53 := by
  constructor
  · rw [Gv_eq_T 53 (by norm_num)]
    exact EqAv 53 (by norm_num)
  · rw [gv_eq_T 53 (by norm_num)]
    exact DnAv 53 (by norm_num)

theorem bnd_54 : Gv 54 = -5878323370 ∧ LOG1E13LB ≤ gv 54 := by
  constructor
  · rw [Gv_eq_T 54 (by norm_num)]
    exact EqAv 54 (by norm_num)
  · rw [gv_eq_T 54 (by norm_num)]
    exact DnAv 54 (by norm_num)

theorem bnd_55 : Gv 55 = -5588273048 ∧ LOG1E13LB ≤ gv 55 := by
  constructor
  · rw [Gv_eq_T 55 (by norm_num)]
    exact EqAv 55 (by norm_num)
  · rw [gv_eq_T 55 (by norm_num)]
    exact DnAv 55 (by norm_num)

theorem bnd_56 : Gv 56 = -5307054506 ∧ LOG1E13LB ≤ gv 56 := by
  constructor
  · rw [Gv_eq_T 56 (by norm_num)]
    exact EqAv 56 (by norm_num)
  · rw [gv_eq_T 56 (by norm_num)]
    exact DnAv 56 (by norm_num)

theorem bnd_57 : Gv 57 = -5034360090 ∧ LOG1E13LB ≤ gv 57 := by
  constructor
  · rw [Gv_eq_T 57 (by norm_num)]
    exact EqAv 57 (by norm_num)
  · rw [gv_eq_T 57 (by norm_num)]
    exact DnAv 57 (by norm_num)

theorem bnd_58 : Gv 58 = -4769929002 ∧ LOG1E13LB ≤ gv 58 := by
  constructor
  · rw [Gv_eq_T 58 (by norm_num)]
    exact EqAv 58 (by norm_num)
  · rw [gv_eq_T 58 (by norm_num)]
    exact DnAv 58 (by norm_num)

theorem bnd_59 : Gv 59 = -4513477590 ∧ LOG1E13LB ≤ gv 59 := by
  constructor
  · rw [Gv_eq_T 59 (by norm_num)]
    exact EqAv 59 (by norm_num)
  · rw [gv_eq_T 59 (by norm_num)]
    exact DnAv 59 (by norm_num)

theorem bnd_60 : Gv 60 = -4264803746 ∧ LOG1E13LB ≤ gv 60 := by
  constructor
  · rw [Gv_eq_T 60 (by norm_num)]
    exact EqAv 60 (by norm_num)
  · rw [gv_eq_T 60 (by norm_num)]
    exact DnAv 60 (by norm_num)

theorem bnd_61 : Gv 61 = -4023616856 ∧ LOG1E13LB ≤ gv 61 := by
  constructor
  · rw [Gv_eq_T 61 (by norm_num)]
    exact EqAv 61 (by norm_num)
  · rw [gv_eq_T 61 (by norm_num)]
    exact DnAv 61 (by norm_num)

theorem bnd_62 : Gv 62 = -3789687278 ∧ LOG1E13LB ≤ gv 62 := by
  constructor
  · rw [Gv_eq_T 62 (by norm_num)]
    exact EqAv 62 (by norm_num)
  · rw [gv_eq_T 62 (by norm_num)]
    exact DnAv 62 (by norm_num)

theorem bnd_63 : Gv 63 = -3562809758 ∧ LOG1E13LB ≤ gv 63 := by
  constructor
  · rw [Gv_eq_T 63 (by norm_num)]
    exact EqAv 63 (by norm_num)
  · rw [gv_eq_T 63 (by norm_num)]
    exact DnAv 63 (by norm_num)

theorem bnd_64 : Gv 64 = -3342787608 ∧ LOG1E13LB ≤ gv 64 := by
  constructor
  · rw [Gv_eq_T 64 (by norm_num)]
    exact EqAv 64 (by norm_num)
  · rw [gv_eq_T 64 (by norm_num)]
    exact DnAv 64 (by norm_num)

theorem bnd_65 : Gv 65 = -3129410440 ∧ LOG1E13LB ≤ gv 65 := by
  constructor
  · rw [Gv_eq_T 65 (by norm_num)]
    exact EqAv 65 (by norm_num)
  · rw [gv_eq_T 65 (by norm_num)]
    exact DnAv 65 (by norm_num)

theorem bnd_66 : Gv 66 = -2922514224 ∧ LOG1E13LB ≤ gv 66 := by
  constructor
  · rw [Gv_eq_T 66 (by norm_num)]
    exact EqAv 66 (by norm_num)
  · rw [gv_eq_T 66 (by norm_num)]
    exact DnAv 66 (by norm_num)

theorem bnd_67 : Gv 67 = -2721927652 ∧ LOG1E13LB ≤ gv 67 := by
  constructor
  · rw [Gv_eq_T 67 (by norm_num)]
    exact EqAv 67 (by norm_num)
  · rw [gv_eq_T 67 (by norm_num)]
    exact DnAv 67 (by norm_num)

theorem bnd_68 : Gv 68 = -2527543040 ∧ LOG1E13LB ≤ gv 68 := by
  constructor
  · rw [Gv_eq_T 68 (by norm_num)]
    exact EqAv 68 (by norm_num)
  · rw [gv_eq_T 68 (by norm_num)]
    exact DnAv 68 (by norm_num)

theorem bnd_69 : Gv 69 = -2339210488 ∧ LOG1E13LB ≤ gv 69 := by
  constructor
  · rw [Gv_eq_T 69 (by norm_num)]
    exact EqAv 69 (by norm_num)
  · rw [gv_eq_T 69 (by norm_num)]
    exact DnAv 69 (by norm_num)

theorem bnd_70 : Gv 70 = -2156806590 ∧ LOG1E13LB ≤ gv 70 := by
  constructor
  · rw [Gv_eq_T 70 (by norm_num)]
    exact EqAv 70 (by norm_num)
  · rw [gv_eq_T 70 (by norm_num)]
    exact DnAv 70 (by norm_num)

theorem bnd_71 : Gv 71 = -1980246712 ∧ LOG1E13LB ≤ gv 71 := by
  constructor
  · rw [Gv_eq_T 71 (by norm_num)]
    exact EqAv 71 (by norm_num)
  · rw [gv_eq_T 71 (by norm_num)]
    exact DnAv 71 (by norm_num)

theorem bnd_72 : Gv 72 = -1809428720 ∧ LOG1E13LB ≤ gv 72 := by
  constructor
  · rw [Gv_eq_T 72 (by norm_num)]
    exact EqAv 72 (by norm_num)
  · rw [gv_eq_T 72 (by norm_num)]
    exact DnAv 72 (by norm_num)

theorem bnd_73 : Gv 73 = -1644271786 ∧ LOG1E13LB ≤ gv 73 := by
  constructor
  · rw [Gv_eq_T 73 (by norm_num)]
    exact EqAv 73 (by norm_num)
  · rw [gv_eq_T 73 (by norm_num)]
    exact DnAv 73 (by norm_num)

theorem bnd_74 : Gv 74 = -1484669366 ∧ LOG1E13LB ≤ gv 74 := by
  constructor
  · rw [Gv_eq_T 74 (by norm_num)]
    exact EqAv 74 (by norm_num)
  · rw [gv_eq_T 74 (by norm_num)]
    exact DnAv 74 (by norm_num)

theorem bnd_75 : Gv 75 = -1330545638 ∧ LOG1E13LB ≤ gv 75 := by
  constructor
  · rw [Gv_eq_T 75 (by norm_num)]
    exact EqAv 75 (by norm_num)
  · rw [gv_eq_T 75 (by norm_num)]
    exact DnAv 75 (by norm_num)

theorem bnd_76 : Gv 76 = -1181797006 ∧ LOG1E13LB ≤ gv 76 := by
  constructor
  · rw [Gv_eq_T 76 (by norm_num)]
    exact EqAv 76 (by norm_num)
  · rw [gv_eq_T 76 (by norm_num)]
    exact DnAv 76 (by norm_num)

theorem bnd_77 : Gv 77 = -1038314510 ∧ LOG1E13LB ≤ gv 77 := by
  constructor
  · rw [Gv_eq_T 77 (by norm_num)]
    exact EqAv 77 (by norm_num)
  · rw [gv_eq_T 77 (by norm_num)]
    exact DnAv 77 (by norm_num)

theorem bnd_78 : Gv 78 = -899959724 ∧ LOG1E13LB ≤ gv 78 := by
  constructor
  · rw [Gv_eq_T 78 (by norm_num)]
    exact EqAv 78 (by norm_num)
  · rw [gv_eq_T 78 (by norm_num)]
    exact DnAv 78 (by norm_num)

theorem bnd_79 : Gv 79 = -766621094 ∧ LOG1E13LB ≤ gv 79 := by
  constructor
  · rw [Gv_eq_T 79 (by norm_num)]
    exact EqAv 79 (by norm_num)
  · rw [gv_eq_T 79 (by norm_num)]
    exact DnAv 79 (by norm_num)

theorem bnd_80 : Gv 80 = -638081134 ∧ LOG1E13LB ≤ gv 80 := by
  constructor
  · rw [Gv_eq_T 80 (by norm_num)]
    exact EqAv 80 (by norm_num)
  · rw [gv_eq_T 80 (by norm_num)]
    exact DnAv 80 (by norm_num)

theorem bnd_81 : Gv 81 = -514184488 ∧ LOG1E13LB ≤ gv 81 := by
  constructor
  · rw [Gv_eq_T 81 (by norm_num)]
    exact EqAv 81 (by norm_num)
  · rw [gv_eq_T 81 (by norm_num)]
    exact DnAv 81 (by norm_num)

theorem bnd_82 : Gv 82 = -394683382 ∧ LOG1E13LB ≤ gv 82 := by
  constructor
  · rw [Gv_eq_T 82 (by norm_num)]
    exact EqAv 82 (by norm_num)
  · rw [gv_eq_T 82 (by norm_num)]
    exact DnAv 82 (by norm_num)

theorem bnd_83 : Gv 83 = -279321540 ∧ LOG1E13LB ≤ gv 83 := by
  constructor
  · rw [Gv_eq_T 83 (by norm_num)]
    exact EqAv 83 (by norm_num)
  · rw [gv_eq_T 83 (by norm_num)]
    exact DnAv 83 (by norm_num)

theorem bnd_84 : Gv 84 = -167824166 ∧ LOG1E13LB ≤ gv 84 := by
  constructor
  · rw [Gv_eq_T 84 (by norm_num)]
    exact EqAv 84 (by norm_num)
  · rw [gv_eq_T 84 (by norm_num)]
    exact DnAv 84 (by norm_num)

theorem bnd_85 : Gv 85 = -59870816 ∧ LOG1E13LB ≤ gv 85 := by
  constructor
  · rw [Gv_eq_T 85 (by norm_num)]
    exact EqAv 85 (by norm_num)
  · rw [gv_eq_T 85 (by norm_num)]
    exact DnAv 85 (by norm_num)

theorem bnd_86 : Gv 86 = 44897908 ∧ LOG1E13LB ≤ gv 86 := by
  constructor
  · rw [Gv_eq_T 86 (by norm_num)]
    exact EqAv 86 (by norm_num)
  · rw [gv_eq_T 86 (by norm_num)]
    exact DnAv 86 (by norm_num)

theorem bnd_87 : Gv 87 = 146876684 ∧ LOG1E13LB ≤ gv 87 := by
  constructor
  · rw [Gv_eq_T 87 (by norm_num)]
    exact EqAv 87 (by norm_num)
  · rw [gv_eq_T 87 (by norm_num)]
    exact DnAv 87 (by norm_num)

theorem bnd_88 : Gv 88 = 246421760 ∧ LOG1E13LB ≤ gv 88 := by
  constructor
  · rw [Gv_eq_T 88 (by norm_num)]
    exact EqAv 88 (by norm_num)
  · rw [gv_eq_T 88 (by norm_num)]
    exact DnAv 88 (by norm_num)

theorem bnd_89 : Gv 89 = 343998064 ∧ LOG1E13LB ≤ gv 89 := by
  constructor
  · rw [Gv_eq_T 89 (by norm_num)]
    exact EqAv 89 (by norm_num)
  · rw [gv_eq_T 89 (by norm_num)]
    exact DnAv 89 (by norm_num)

theorem bnd_90 : Gv 90 = 440046778 ∧ LOG1E13LB ≤ gv 90 := by
  constructor
  · rw [Gv_eq_T 90 (by norm_num)]
    exact EqAv 90 (by norm_num)
  · rw [gv_eq_T 90 (by norm_num)]
    exact DnAv 90 (by norm_num)

theorem bnd_91 : Gv 91 = 535010436 ∧ LOG1E13LB ≤ gv 91 := by
  constructor
  · rw [Gv_eq_T 91 (by norm_num)]
    exact EqAv 91 (by norm_num)
  · rw [gv_eq_T 91 (by norm_num)]
    exact DnAv 91 (by norm_num)

theorem bnd_92 : Gv 92 = 629355242 ∧ LOG1E13LB ≤ gv 92 := by
  constructor
  · rw [Gv_eq_T 92 (by norm_num)]
    exact EqAv 92 (by norm_num)
  · rw [gv_eq_T 92 (by norm_num)]
    exact DnAv 92 (by norm_num)

theorem bnd_93 : Gv 93 = 723571658 ∧ LOG1E13LB ≤ gv 93 := by
  constructor
  · rw [Gv_eq_T 93 (by norm_num)]
    exact EqAv 93 (by norm_num)
  · rw [gv_eq_T 93 (by norm_num)]
    exact DnAv 93 (by norm_num)

theorem bnd_94 : Gv 94 = 818099530 ∧ LOG1E13LB ≤ gv 94 := by
  constructor
  · rw [Gv_eq_T 94 (by norm_num)]
    exact EqAv 94 (by norm_num)
  · rw [gv_eq_T 94 (by norm_num)]
    exact DnAv 94 (by norm_num)

theorem bnd_95 : Gv 95 = 913385520 ∧ LOG1E13LB ≤ gv 95 := by
  constructor
  · rw [Gv_eq_T 95 (by norm_num)]
    exact EqAv 95 (by norm_num)
  · rw [gv_eq_T 95 (by norm_num)]
    exact DnAv 95 (by norm_num)

theorem bnd_96 : Gv 96 = 1009898406 ∧ LOG1E13LB ≤ gv 96 := by
  constructor
  · rw [Gv_eq_T 96 (by norm_num)]
    exact EqAv 96 (by norm_num)
  · rw [gv_eq_T 96 (by norm_num)]
    exact DnAv 96 (by norm_num)

theorem bnd_97 : Gv 97 = 1108013850 ∧ LOG1E13LB ≤ gv 97 := by
  constructor
  · rw [Gv_eq_T 97 (by norm_num)]
    exact EqAv 97 (by norm_num)
  · rw [gv_eq_T 97 (by norm_num)]
    exact DnAv 97 (by norm_num)

theorem bnd_98 : Gv 98 = 1208130042 ∧ LOG1E13LB ≤ gv 98 := by
  constructor
  · rw [Gv_eq_T 98 (by norm_num)]
    exact EqAv 98 (by norm_num)
  · rw [gv_eq_T 98 (by norm_num)]
    exact DnAv 98 (by norm_num)

theorem bnd_99 : Gv 99 = 1310591974 ∧ LOG1E13LB ≤ gv 99 := by
  constructor
  · rw [Gv_eq_T 99 (by norm_num)]
    exact EqAv 99 (by norm_num)
  · rw [gv_eq_T 99 (by norm_num)]
    exact DnAv 99 (by norm_num)

theorem bnd_100 : Gv 100 = 1415700272 ∧ LOG1E13LB ≤ gv 100 := by
  constructor
  · rw [Gv_eq_T 100 (by norm_num)]
    exact EqAv 100 (by norm_num)
  · rw [gv_eq_T 100 (by norm_num)]
    exact DnAv 100 (by norm_num)

theorem bnd_101 : Gv 101 = 1523730418 ∧ LOG1E13LB ≤ gv 101 := by
  constructor
  · rw [Gv_eq_T 101 (by norm_num)]
    exact EqAv 101 (by norm_num)
  · rw [gv_eq_T 101 (by norm_num)]
    exact DnAv 101 (by norm_num)

theorem bnd_102 : Gv 102 = 1634896702 ∧ LOG1E13LB ≤ gv 102 := by
  constructor
  · rw [Gv_eq_T 102 (by norm_num)]
    exact EqAv 102 (by norm_num)
  · rw [gv_eq_T 102 (by norm_num)]
    exact DnAv 102 (by norm_num)

theorem bnd_103 : Gv 103 = 1749350620 ∧ LOG1E13LB ≤ gv 103 := by
  constructor
  · rw [Gv_eq_T 103 (by norm_num)]
    exact EqAv 103 (by norm_num)
  · rw [gv_eq_T 103 (by norm_num)]
    exact DnAv 103 (by norm_num)

theorem bnd_104 : Gv 104 = 1867200246 ∧ LOG1E13LB ≤ gv 104 := by
  constructor
  · rw [Gv_eq_T 104 (by norm_num)]
    exact EqAv 104 (by norm_num)
  · rw [gv_eq_T 104 (by norm_num)]
    exact DnAv 104 (by norm_num)

theorem bnd_105 : Gv 105 = 1988504702 ∧ LOG1E13LB ≤ gv 105 := by
  constructor
  · rw [Gv_eq_T 105 (by norm_num)]
    exact EqAv 105 (by norm_num)
  · rw [gv_eq_T 105 (by norm_num)]
    exact DnAv 105 (by norm_num)

theorem bnd_106 : Gv 106 = 2113236740 ∧ LOG1E13LB ≤ gv 106 := by
  constructor
  · rw [Gv_eq_T 106 (by norm_num)]
    exact EqAv 106 (by norm_num)
  · rw [gv_eq_T 106 (by norm_num)]
    exact DnAv 106 (by norm_num)

theorem bnd_107 : Gv 107 = 2241353770 ∧ LOG1E13LB ≤ gv 107 := by
  constructor
  · rw [Gv_eq_T 107 (by norm_num)]
    exact EqAv 107 (by norm_num)
  · rw [gv_eq_T 107 (by norm_num)]
    exact DnAv 107 (by norm_num)

theorem bnd_108 : Gv 108 = 2372725910 ∧ LOG1E13LB ≤ gv 108 := by
  constructor
  · rw [Gv_eq_T 108 (by norm_num)]
    exact EqAv 108 (by norm_num)
  · rw [gv_eq_T 108 (by norm_num)]
    exact DnAv 108 (by norm_num)

theorem bnd_109 : Gv 109 = 2507158882 ∧ LOG1E13LB ≤ gv 109 := by
  constructor
  · rw [Gv_eq_T 109 (by norm_num)]
    exact EqAv 109 (by norm_num)
  · rw [gv_eq_T 109 (by norm_num)]
    exact DnAv 109 (by norm_num)

theorem bnd_110 : Gv 110 = 2644409468 ∧ LOG1E13LB ≤ gv 110 := by
  constructor
  · rw [Gv_eq_T 110 (by norm_num)]
    exact EqAv 110 (by norm_num)
  · rw [gv_eq_T 110 (by norm_num)]
    exact DnAv 110 (by norm_num)

theorem bnd_111 : Gv 111 = 2784172476 ∧ LOG1E13LB ≤ gv 111 := by
  constructor
  · rw [Gv_eq_T 111 (by norm_num)]
    exact EqAv 111 (by norm_num)
  · rw [gv_eq_T 111 (by norm_num)]
    exact DnAv 111 (by norm_num)

theorem bnd_112 : Gv 112 = 2926089128 ∧ LOG1E13LB ≤ gv 112 := by
  constructor
  · rw [Gv_eq_T 112 (by norm_num)]
    exact EqAv 112 (by norm_num)
  · rw [gv_eq_T 112 (by norm_num)]
    exact DnAv 112 (by norm_num)

theorem bnd_113 : Gv 113 = 3069717462 ∧ LOG1E13LB ≤ gv 113 := by
  constructor
  · rw [Gv_eq_T 113 (by norm_num)]
    exact EqAv 113 (by norm_num)
  · rw [gv_eq_T 113 (by norm_num)]
    exact DnAv 113 (by norm_num)

theorem bnd_114 : Gv 114 = 3214572748 ∧ LOG1E13LB ≤ gv 114 := by
  constructor
  · rw [Gv_eq_T 114 (by norm_num)]
    exact EqAv 114 (by norm_num)
  · rw [gv_eq_T 114 (by norm_num)]
    exact DnAv 114 (by norm_num)

theorem bnd_115 : Gv 115 = 3360124178 ∧ LOG1E13LB ≤ gv 115 := by
  constructor
  · rw [Gv_eq_T 115 (by norm_num)]
    exact EqAv 115 (by norm_num)
  · rw [gv_eq_T 115 (by norm_num)]
    exact DnAv 115 (by norm_num)

theorem bnd_116 : Gv 116 = 3505769630 ∧ LOG1E13LB ≤ gv 116 := by
  constructor
  · rw [Gv_eq_T 116 (by norm_num)]
    exact EqAv 116 (by norm_num)
  · rw [gv_eq_T 116 (by norm_num)]
    exact DnAv 116 (by norm_num)

theorem bnd_117 : Gv 117 = 3650844258 ∧ LOG1E13LB ≤ gv 117 := by
  constructor
  · rw [Gv_eq_T 117 (by norm_num)]
    exact EqAv 117 (by norm_num)
  · rw [gv_eq_T 117 (by norm_num)]
    exact DnAv 117 (by norm_num)

theorem bnd_118 : Gv 118 = 3794651054 ∧ LOG1E13LB ≤ gv 118 := by
  constructor
  · rw [Gv_eq_T 118 (by norm_num)]
    exact EqAv 118 (by norm_num)
  · rw [gv_eq_T 118 (by norm_num)]
    exact DnAv 118 (by norm_num)

theorem bnd_119 : Gv 119 = 3936427824 ∧ LOG1E13LB ≤ gv 119 := by
  constructor
  · rw [Gv_eq_T 119 (by norm_num)]
    exact EqAv 119 (by norm_num)
  · rw [gv_eq_T 119 (by norm_num)]
    exact DnAv 119 (by norm_num)

theorem bnd_120 : Gv 120 = 4075351810 ∧ LOG1E13LB ≤ gv 120 := by
  constructor
  · rw [Gv_eq_T 120 (by norm_num)]
    exact EqAv 120 (by norm_num)
  · rw [gv_eq_T 120 (by norm_num)]
    exact DnAv 120 (by norm_num)

theorem bnd_121 : Gv 121 = 4210622934 ∧ LOG1E13LB ≤ gv 121 := by
  constructor
  · rw [Gv_eq_T 121 (by norm_num)]
    exact EqAv 121 (by norm_num)
  · rw [gv_eq_T 121 (by norm_num)]
    exact DnAv 121 (by norm_num)

theorem bnd_122 : Gv 122 = 4341339132 ∧ LOG1E13LB ≤ gv 122 := by
  constructor
  · rw [Gv_eq_T 122 (by norm_num)]
    exact EqAv 122 (by norm_num)
  · rw [gv_eq_T 122 (by norm_num)]
    exact DnAv 122 (by norm_num)

theorem bnd_123 : Gv 123 = 4466614254 ∧ LOG1E13LB ≤ gv 123 := by
  constructor
  · rw [Gv_eq_T 123 (by norm_num)]
    exact EqAv 123 (by norm_num)
  · rw [gv_eq_T 123 (by norm_num)]
    exact DnAv 123 (by norm_num)

theorem bnd_124 : Gv 124 = 4585538558 ∧ LOG1E13LB ≤ gv 124 := by
  constructor
  · rw [Gv_eq_T 124 (by norm_num)]
    exact EqAv 124 (by norm_num)
  · rw [gv_eq_T 124 (by norm_num)]
    exact DnAv 124 (by norm_num)

theorem bnd_125 : Gv 125 = 4697213228 ∧ LOG1E13LB ≤ gv 125 := by
  constructor
  · rw [Gv_eq_T 125 (by norm_num)]
    exact EqAv 125 (by norm_num)
  · rw [gv_eq_T 125 (by norm_num)]
    exact DnAv 125 (by norm_num)

theorem bnd_126 : Gv 126 = 4800748494 ∧ LOG1E13LB ≤ gv 126 := by
  constructor
  · rw [Gv_eq_T 126 (by norm_num)]
    exact EqAv 126 (by norm_num)
  · rw [gv_eq_T 126 (by norm_num)]
    exact DnAv 126 (by norm_num)

theorem bnd_127 : Gv 127 = 4895267072 ∧ LOG1E13LB ≤ gv 127 := by
  constructor
  · rw [Gv_eq_T 127 (by norm_num)]
    exact EqAv 127 (by norm_num)
  · rw [gv_eq_T 127 (by norm_num)]
    exact DnAv 127 (by norm_num)

theorem bnd_128 : Gv 128 = 4979937826 ∧ LOG1E13LB ≤ gv 128 := by
  constructor
  · rw [Gv_eq_T 128 (by norm_num)]
    exact EqBv 0 (by norm_num)
  · rw [gv_eq_T 128 (by norm_num)]
    exact DnBv 0 (by norm_num)

theorem bnd_129 : Gv 129 = 5053983574 ∧ LOG1E13LB ≤ gv 129 := by
  constructor
  · rw [Gv_eq_T 129 (by norm_num)]
    exact EqBv 1 (by norm_num)
  · rw [gv_eq_T 129 (by norm_num)]
    exact DnBv 1 (by norm_num)

theorem bnd_130 : Gv 130 = 5116707614 ∧ LOG1E13LB ≤ gv 130 := by
  constructor
  · rw [Gv_eq_T 130 (by norm_num)]
    exact EqBv 2 (by norm_num)
  · rw [gv_eq_T 130 (by norm_num)]
    exact DnBv 2 (by norm_num)

theorem bnd_131 : Gv 131 = 5167505784 ∧ LOG1E13LB ≤ gv 131 := by
  constructor
  · rw [Gv_eq_T 131 (by norm_num)]
    exact EqBv 3 (by norm_num)
  · rw [gv_eq_T 131 (by norm_num)]
    exact DnBv 3 (by norm_num)

theorem bnd_132 : Gv 132 = 5205812254 ∧ LOG1E13LB ≤ gv 132 := by
  constructor
  · rw [Gv_eq_T 132 (by norm_num)]
    exact EqBv 4 (by norm_num)
  · rw [gv_eq_T 132 (by norm_num)]
    exact DnBv 4 (by norm_num)

theorem bnd_133 : Gv 133 = 5231240080 ∧ LOG1E13LB ≤ gv 133 := by
  constructor
  · rw [Gv_eq_T 133 (by norm_num)]
    exact EqBv 5 (by norm_num)
  · rw [gv_eq_T 133 (by norm_num)]
    exact DnBv 5 (by norm_num)

theorem bnd_134 : Gv 134 = 5243462640 ∧ LOG1E13LB ≤ gv 134 := by
  constructor
  · rw [Gv_eq_T 134 (by norm_num)]
    exact EqBv 6 (by norm_num)
  · rw [gv_eq_T 134 (by norm_num)]
    exact DnBv 6 (by norm_num)

theorem bnd_135 : Gv 135 = 5243547840 ∧ LOG1E13LB ≤ gv 135 := by
  constructor
  · rw [Gv_eq_T 135 (by norm_num)]
    exact EqBv 7 (by norm_num)
  · rw [gv_eq_T 135 (by norm_num)]
    exact DnBv 7 (by norm_num)

theorem bnd_136 : Gv 136 = 5242405072 ∧ LOG1E13LB ≤ gv 136 := by
  constructor
  · rw [Gv_eq_T 136 (by norm_num)]
    exact EqBv 8 (by norm_num)
  · rw [gv_eq_T 136 (by norm_num)]
    exact DnBv 8 (by norm_num)

theorem bnd_137 : Gv 137 = 5227817030 ∧ LOG1E13LB ≤ gv 137 := by
  constructor
  · rw [Gv_eq_T 137 (by norm_num)]
    exact EqBv 9 (by norm_num)
  · rw [gv_eq_T 137 (by norm_num)]
    exact DnBv 9 (by norm_num)

theorem bnd_138 : Gv 138 = 5199860940 ∧ LOG1E13LB ≤ gv 138 := by
  constructor
  · rw [Gv_eq_T 138 (by norm_num)]
    exact EqBv 10 (by norm_num)
  · rw [gv_eq_T 138 (by norm_num)]
    exact DnBv 10 (by norm_num)

theorem bnd_139 : Gv 139 = 5158698200 ∧ LOG1E13LB ≤ gv 139 := by
  constructor
  · rw [Gv_eq_T 139 (by norm_num)]
    exact EqBv 11 (by norm_num)
  · rw [gv_eq_T 139 (by norm_num)]
    exact DnBv 11 (by norm_num)

theorem bnd_140 : Gv 140 = 5104649734 ∧ LOG1E13LB ≤ gv 140 := by
  constructor
  · rw [Gv_eq_T 140 (by norm_num)]
    exact EqBv 12 (by norm_num)
  · rw [gv_eq_T 140 (by norm_num)]
    exact DnBv 12 (by norm_num)

theorem bnd_141 : Gv 141 = 5038136542 ∧ LOG1E13LB ≤ gv 141 := by
  constructor
  · rw [Gv_eq_T 141 (by norm_num)]
    exact EqBv 13 (by norm_num)
  · rw [gv_eq_T 141 (by norm_num)]
    exact DnBv 13 (by norm_num)

theorem bnd_142 : Gv 142 = 4959673416 ∧ LOG1E13LB ≤ gv 142 := by
  constructor
  · rw [Gv_eq_T 142 (by norm_num)]
    exact EqBv 14 (by norm_num)
  · rw [gv_eq_T 142 (by norm_num)]
    exact DnBv 14 (by norm_num)

theorem bnd_143 : Gv 143 = 4869845920 ∧ LOG1E13LB ≤ gv 143 := by
  constructor
  · rw [Gv_eq_T 143 (by norm_num)]
    exact EqBv 15 (by norm_num)
  · rw [gv_eq_T 143 (by norm_num)]
    exact DnBv 15 (by norm_num)

theorem bnd_144 : Gv 144 = 4769325640 ∧ LOG1E13LB ≤ gv 144 := by
  constructor
  · rw [Gv_eq_T 144 (by norm_num)]
    exact EqBv 16 (by norm_num)
  · rw [gv_eq_T 144 (by norm_num)]
    exact DnBv 16 (by norm_num)

theorem bnd_145 : Gv 145 = 4658850564 ∧ LOG1E13LB ≤ gv 145 := by
  constructor
  · rw [Gv_eq_T 145 (by norm_num)]
    exact EqBv 17 (by norm_num)
  · rw [gv_eq_T 145 (by norm_num)]
    exact DnBv 17 (by norm_num)

theorem bnd_146 : Gv 146 = 4539209970 ∧ LOG1E13LB ≤ gv 146 := by
  constructor
  · rw [Gv_eq_T 146 (by norm_num)]
    exact EqBv 18 (by norm_num)
  · rw [gv_eq_T 146 (by norm_num)]
    exact DnBv 18 (by norm_num)

theorem bnd_147 : Gv 147 = 4411171656 ∧ LOG1E13LB ≤ gv 147 := by
  constructor
  · rw [Gv_eq_T 147 (by norm_num)]
    exact EqBv 19 (by norm_num)
  · rw [gv_eq_T 147 (by norm_num)]
    exact DnBv 19 (by norm_num)

theorem bnd_148 : Gv 148 = 4275563124 ∧ LOG1E13LB ≤ gv 148 := by
  constructor
  · rw [Gv_eq_T 148 (by norm_num)]
    exact EqBv 20 (by norm_num)
  · rw [gv_eq_T 148 (by norm_num)]
    exact DnBv 20 (by norm_num)

theorem bnd_149 : Gv 149 = 4133164766 ∧ LOG1E13LB ≤ gv 149 := by
  constructor
  · rw [Gv_eq_T 149 (by norm_num)]
    exact EqBv 21 (by norm_num)
  · rw [gv_eq_T 149 (by norm_num)]
    exact DnBv 21 (by norm_num)

theorem bnd_150 : Gv 150 = 3984788154 ∧ LOG1E13LB ≤ gv 150 := by
  constructor
  · rw [Gv_eq_T 150 (by norm_num)]
    exact EqBv 22 (by norm_num)
  · rw [gv_eq_T 150 (by norm_num)]
    exact DnBv 22 (by norm_num)

theorem bnd_151 : Gv 151 = 3831175128 ∧ LOG1E13LB ≤ gv 151 := by
  constructor
  · rw [Gv_eq_T 151 (by norm_num)]
    exact EqBv 23 (by norm_num)
  · rw [gv_eq_T 151 (by norm_num)]
    exact DnBv 23 (by norm_num)

theorem bnd_152 : Gv 152 = 3673038832 ∧ LOG1E13LB ≤ gv 152 := by
  constructor
  · rw [Gv_eq_T 152 (by norm_num)]
    exact EqBv 24 (by norm_num)
  · rw [gv_eq_T 152 (by norm_num)]
    exact DnBv 24 (by norm_num)

theorem bnd_153 : Gv 153 = 3511050516 ∧ LOG1E13LB ≤ gv 153 := by
  constructor
  · rw [Gv_eq_T 153 (by norm_num)]
    exact EqBv 25 (by norm_num)
  · rw [gv_eq_T 153 (by norm_num)]
    exact DnBv 25 (by norm_num)

theorem bnd_154 : Gv 154 = 3345776754 ∧ LOG1E13LB ≤ gv 154 := by
  constructor
  · rw [Gv_eq_T 154 (by norm_num)]
    exact EqBv 26 (by norm_num)
  · rw [gv_eq_T 154 (by norm_num)]
    exact DnBv 26 (by norm_num)

theorem bnd_155 : Gv 155 = 3177787138 ∧ LOG1E13LB ≤ gv 155 := by
  constructor
  · rw [Gv_eq_T 155 (by norm_num)]
    exact EqBv 27 (by norm_num)
  · rw [gv_eq_T 155 (by norm_num)]
    exact DnBv 27 (by norm_num)

theorem bnd_156 : Gv 156 = 3007522406 ∧ LOG1E13LB ≤ gv 156 := by
  constructor
  · rw [Gv_eq_T 156 (by norm_num)]
    exact EqBv 28 (by norm_num)
  · rw [gv_eq_T 156 (by norm_num)]
    exact DnBv 28 (by norm_num)

theorem bnd_157 : Gv 157 = 2835408548 ∧ LOG1E13LB ≤ gv 157 := by
  constructor
  · rw [Gv_eq_T 157 (by norm_num)]
    exact EqBv 29 (by norm_num)
  · rw [gv_eq_T 157 (by norm_num)]
    exact DnBv 29 (by norm_num)

theorem bnd_158 : Gv 158 = 2661730028 ∧ LOG1E13LB ≤ gv 158 := by
  constructor
  · rw [Gv_eq_T 158 (by norm_num)]
    exact EqBv 30 (by norm_num)
  · rw [gv_eq_T 158 (by norm_num)]
    exact DnBv 30 (by norm_num)

theorem bnd_159 : Gv 159 = 2486740728 ∧ LOG1E13LB ≤ gv 159 := by
  constructor
  · rw [Gv_eq_T 159 (by norm_num)]
    exact EqBv 31 (by norm_num)
  · rw [gv_eq_T 159 (by norm_num)]
    exact DnBv 31 (by norm_num)

theorem bnd_160 : Gv 160 = 2310640166 ∧ LOG1E13LB ≤ gv 160 := by
  constructor
  · rw [Gv_eq_T 160 (by norm_num)]
    exact EqBv 32 (by norm_num)
  · rw [gv_eq_T 160 (by norm_num)]
    exact DnBv 32 (by norm_num)

theorem bnd_161 : Gv 161 = 2133538872 ∧ LOG1E13LB ≤ gv 161 := by
  constructor
  · rw [Gv_eq_T 161 (by norm_num)]
    exact EqBv 33 (by norm_num)
  · rw [gv_eq_T 161 (by norm_num)]
    exact DnBv 33 (by norm_num)

theorem bnd_162 : Gv 162 = 1955506462 ∧ LOG1E13LB ≤ gv 162 := by
  constructor
  · rw [Gv_eq_T 162 (by norm_num)]
    exact EqBv 34 (by norm_num)
  · rw [gv_eq_T 162 (by norm_num)]
    exact DnBv 34 (by norm_num)

theorem bnd_163 : Gv 163 = 1776536308 ∧ LOG1E13LB ≤ gv 163 := by
  constructor
  · rw [Gv_eq_T 163 (by norm_num)]
    exact EqBv 35 (by norm_num)
  · rw [gv_eq_T 163 (by norm_num)]
    exact DnBv 35 (by norm_num)

theorem bnd_164 : Gv 164 = 1596612170 ∧ LOG1E13LB ≤ gv 164 := by
  constructor
  · rw [Gv_eq_T 164 (by norm_num)]
    exact EqBv 36 (by norm_num)
  · rw [gv_eq_T 164 (by norm_num)]
    exact DnBv 36 (by norm_num)

theorem bnd_165 : Gv 165 = 1415663902 ∧ LOG1E13LB ≤ gv 165 := by
  constructor
  · rw [Gv_eq_T 165 (by norm_num)]
    exact EqBv 37 (by norm_num)
  · rw [gv_eq_T 165 (by norm_num)]
    exact DnBv 37 (by norm_num)

theorem bnd_166 : Gv 166 = 1233608330 ∧ LOG1E13LB ≤ gv 166 := by
  constructor
  · rw [Gv_eq_T 166 (by norm_num)]
    exact EqBv 38 (by norm_num)
  · rw [gv_eq_T 166 (by norm_num)]
    exact DnBv 38 (by norm_num)

theorem bnd_167 : Gv 167 = 1050360020 ∧ LOG1E13LB ≤ gv 167 := by
  constructor
  · rw [Gv_eq_T 167 (by norm_num)]
    exact EqBv 39 (by norm_num)
  · rw [gv_eq_T 167 (by norm_num)]
    exact DnBv 39 (by norm_num)

theorem bnd_168 : Gv 168 = 865814458 ∧ LOG1E13LB ≤ gv 168 := by
  constructor
  · rw [Gv_eq_T 168 (by norm_num)]
    exact EqBv 40 (by norm_num)
  · rw [gv_eq_T 168 (by norm_num)]
    exact DnBv 40 (by norm_num)

theorem bnd_169 : Gv 169 = 679912960 ∧ LOG1E13LB ≤ gv 169 := by
  constructor
  · rw [Gv_eq_T 169 (by norm_num)]
    exact EqBv 41 (by norm_num)
  · rw [gv_eq_T 169 (by norm_num)]
    exact DnBv 41 (by norm_num)

theorem bnd_170 : Gv 170 = 492562498 ∧ LOG1E13LB ≤ gv 170 := by
  constructor
  · rw [Gv_eq_T 170 (by norm_num)]
    exact EqBv 42 (by norm_num)
  · rw [gv_eq_T 170 (by norm_num)]
    exact DnBv 42 (by norm_num)

theorem bnd_171 : Gv 171 = 303784204 ∧ LOG1E13LB ≤ gv 171 := by
  constructor
  · rw [Gv_eq_T 171 (by norm_num)]
    exact EqBv 43 (by norm_num)
  · rw [gv_eq_T 171 (by norm_num)]
    exact DnBv 43 (by norm_num)

theorem bnd_172 : Gv 172 = 113606814 ∧ LOG1E13LB ≤ gv 172 := by
  constructor
  · rw [Gv_eq_T 172 (by norm_num)]
    exact EqBv 44 (by norm_num)
  · rw [gv_eq_T 172 (by norm_num)]
    exact DnBv 44 (by norm_num)

theorem bnd_173 : Gv 173 = -77868546 ∧ LOG1E13LB ≤ gv 173 := by
  constructor
  · rw [Gv_eq_T 173 (by norm_num)]
    exact EqBv 45 (by norm_num)
  · rw [gv_eq_T 173 (by norm_num)]
    exact DnBv 45 (by norm_num)

theorem bnd_174 : Gv 174 = -270494066 ∧ LOG1E13LB ≤ gv 174 := by
  constructor
  · rw [Gv_eq_T 174 (by norm_num)]
    exact EqBv 46 (by norm_num)
  · rw [gv_eq_T 174 (by norm_num)]
    exact DnBv 46 (by norm_num)

theorem bnd_175 : Gv 175 = -463983814 ∧ LOG1E13LB ≤ gv 175 := by
  constructor
  · rw [Gv_eq_T 175 (by norm_num)]
    exact EqBv 47 (by norm_num)
  · rw [gv_eq_T 175 (by norm_num)]
    exact DnBv 47 (by norm_num)

theorem bnd_176 : Gv 176 = -657983330 ∧ LOG1E13LB ≤ gv 176 := by
  constructor
  · rw [Gv_eq_T 176 (by norm_num)]
    exact EqBv 48 (by norm_num)
  · rw [gv_eq_T 176 (by norm_num)]
    exact DnBv 48 (by norm_num)

theorem bnd_177 : Gv 177 = -852040354 ∧ LOG1E13LB ≤ gv 177 := by
  constructor
  · rw [Gv_eq_T 177 (by norm_num)]
    exact EqBv 49 (by norm_num)
  · rw [gv_eq_T 177 (by norm_num)]
    exact DnBv 49 (by norm_num)

theorem bnd_178 : Gv 178 = -1045582650 ∧ LOG1E13LB ≤ gv 178 := by
  constructor
  · rw [Gv_eq_T 178 (by norm_num)]
    exact EqBv 50 (by norm_num)
  · rw [gv_eq_T 178 (by norm_num)]
    exact DnBv 50 (by norm_num)

theorem bnd_179 : Gv 179 = -1237915124 ∧ LOG1E13LB ≤ gv 179 := by
  constructor
  · rw [Gv_eq_T 179 (by norm_num)]
    exact EqBv 51 (by norm_num)
  · rw [gv_eq_T 179 (by norm_num)]
    exact DnBv 51 (by norm_num)

theorem bnd_180 : Gv 180 = -1428232314 ∧ LOG1E13LB ≤ gv 180 := by
  constructor
  · rw [Gv_eq_T 180 (by norm_num)]
    exact EqBv 52 (by norm_num)
  · rw [gv_eq_T 180 (by norm_num)]
    exact DnBv 52 (by norm_num)

theorem bnd_181 : Gv 181 = -1615603014 ∧ LOG1E13LB ≤ gv 181 := by
  constructor
  · rw [Gv_eq_T 181 (by norm_num)]
    exact EqBv 53 (by norm_num)
  · rw [gv_eq_T 181 (by norm_num)]
    exact DnBv 53 (by norm_num)

theorem bnd_182 : Gv 182 = -1798966248 ∧ LOG1E13LB ≤ gv 182 := by
  constructor
  · rw [Gv_eq_T 182 (by norm_num)]
    exact EqBv 54 (by norm_num)
  · rw [gv_eq_T 182 (by norm_num)]
    exact DnBv 54 (by norm_num)

theorem bnd_183 : Gv 183 = -1977196588 ∧ LOG1E13LB ≤ gv 183 := by
  constructor
  · rw [Gv_eq_T 183 (by norm_num)]
    exact EqBv 55 (by norm_num)
  · rw [gv_eq_T 183 (by norm_num)]
    exact DnBv 55 (by norm_num)

theorem bnd_184 : Gv 184 = -2149002426 ∧ LOG1E13LB ≤ gv 184 := by
  constructor
  · rw [Gv_eq_T 184 (by norm_num)]
    exact EqBv 56 (by norm_num)
  · rw [gv_eq_T 184 (by norm_num)]
    exact DnBv 56 (by norm_num)

theorem bnd_185 : Gv 185 = -2313032060 ∧ LOG1E13LB ≤ gv 185 := by
  constructor
  · rw [Gv_eq_T 185 (by norm_num)]
    exact EqBv 57 (by norm_num)
  · rw [gv_eq_T 185 (by norm_num)]
    exact DnBv 57 (by norm_num)

theorem bnd_186 : Gv 186 = -2467878356 ∧ LOG1E13LB ≤ gv 186 := by
  constructor
  · rw [Gv_eq_T 186 (by norm_num)]
    exact EqBv 58 (by norm_num)
  · rw [gv_eq_T 186 (by norm_num)]
    exact DnBv 58 (by norm_num)

theorem bnd_187 : Gv 187 = -2612057100 ∧ LOG1E13LB ≤ gv 187 := by
  constructor
  · rw [Gv_eq_T 187 (by norm_num)]
    exact EqBv 59 (by norm_num)
  · rw [gv_eq_T 187 (by norm_num)]
    exact DnBv 59 (by norm_num)

theorem bnd_188 : Gv 188 = -2744105634 ∧ LOG1E13LB ≤ gv 188 := by
  constructor
  · rw [Gv_eq_T 188 (by norm_num)]
    exact EqBv 60 (by norm_num)
  · rw [gv_eq_T 188 (by norm_num)]
    exact DnBv 60 (by norm_num)

theorem bnd_189 : Gv 189 = -2862529792 ∧ LOG1E13LB ≤ gv 189 := by
  constructor
  · rw [Gv_eq_T 189 (by norm_num)]
    exact EqBv 61 (by norm_num)
  · rw [gv_eq_T 189 (by norm_num)]
    exact DnBv 61 (by norm_num)

theorem bnd_190 : Gv 190 = -2965902920 ∧ LOG1E13LB ≤ gv 190 := by
  constructor
  · rw [Gv_eq_T 190 (by norm_num)]
    exact EqBv 62 (by norm_num)
  · rw [gv_eq_T 190 (by norm_num)]
    exact DnBv 62 (by norm_num)

theorem bnd_191 : Gv 191 = -3052871576 ∧ LOG1E13LB ≤ gv 191 := by
  constructor
  · rw [Gv_eq_T 191 (by norm_num)]
    exact EqBv 63 (by norm_num)
  · rw [gv_eq_T 191 (by norm_num)]
    exact DnBv 63 (by norm_num)

theorem bnd_192 : Gv 192 = -3122187702 ∧ LOG1E13LB ≤ gv 192 := by
  constructor
  · rw [Gv_eq_T 192 (by norm_num)]
    exact EqBv 64 (by norm_num)
  · rw [gv_eq_T 192 (by norm_num)]
    exact DnBv 64 (by norm_num)

theorem bnd_193 : Gv 193 = -3172774766 ∧ LOG1E13LB ≤ gv 193 := by
  constructor
  · rw [Gv_eq_T 193 (by norm_num)]
    exact EqBv 65 (by norm_num)
  · rw [gv_eq_T 193 (by norm_num)]
    exact DnBv 65 (by norm_num)

theorem bnd_194 : Gv 194 = -3203748306 ∧ LOG1E13LB ≤ gv 194 := by
  constructor
  · rw [Gv_eq_T 194 (by norm_num)]
    exact EqBv 66 (by norm_num)
  · rw [gv_eq_T 194 (by norm_num)]
    exact DnBv 66 (by norm_num)

theorem bnd_195 : Gv 195 = -3204711408 ∧ LOG1E13LB ≤ gv 195 := by
  constructor
  · rw [Gv_eq_T 195 (by norm_num)]
    exact EqBv 67 (by norm_num)
  · rw [gv_eq_T 195 (by norm_num)]
    exact DnBv 67 (by norm_num)

theorem bnd_196 : Gv 196 = -3173703350 ∧ LOG1E13LB ≤ gv 196 := by
  constructor
  · rw [Gv_eq_T 196 (by norm_num)]
    exact EqBv 68 (by norm_num)
  · rw [gv_eq_T 196 (by norm_num)]
    exact DnBv 68 (by norm_num)

theorem bnd_197 : Gv 197 = -3121876890 ∧ LOG1E13LB ≤ gv 197 := by
  constructor
  · rw [Gv_eq_T 197 (by norm_num)]
    exact EqBv 69 (by norm_num)
  · rw [gv_eq_T 197 (by norm_num)]
    exact DnBv 69 (by norm_num)

theorem bnd_198 : Gv 198 = -3049597186 ∧ LOG1E13LB ≤ gv 198 := by
  constructor
  · rw [Gv_eq_T 198 (by norm_num)]
    exact EqBv 70 (by norm_num)
  · rw [gv_eq_T 198 (by norm_num)]
    exact DnBv 70 (by norm_num)

theorem bnd_199 : Gv 199 = -2957526276 ∧ LOG1E13LB ≤ gv 199 := by
  constructor
  · rw [Gv_eq_T 199 (by norm_num)]
    exact EqBv 71 (by norm_num)
  · rw [gv_eq_T 199 (by norm_num)]
    exact DnBv 71 (by norm_num)

theorem bnd_200 : Gv 200 = -2846566798 ∧ LOG1E13LB ≤ gv 200 := by
  constructor
  · rw [Gv_eq_T 200 (by norm_num)]
    exact EqBv 72 (by norm_num)
  · rw [gv_eq_T 200 (by norm_num)]
    exact DnBv 72 (by norm_num)

theorem bnd_201 : Gv 201 = -2717821724 ∧ LOG1E13LB ≤ gv 201 := by
  constructor
  · rw [Gv_eq_T 201 (by norm_num)]
    exact EqBv 73 (by norm_num)
  · rw [gv_eq_T 201 (by norm_num)]
    exact DnBv 73 (by norm_num)

theorem bnd_202 : Gv 202 = -2572671612 ∧ LOG1E13LB ≤ gv 202 := by
  constructor
  · rw [Gv_eq_T 202 (by norm_num)]
    exact EqBv 74 (by norm_num)
  · rw [gv_eq_T 202 (by norm_num)]
    exact DnBv 74 (by norm_num)

theorem bnd_203 : Gv 203 = -2412594668 ∧ LOG1E13LB ≤ gv 203 := by
  constructor
  · rw [Gv_eq_T 203 (by norm_num)]
    exact EqBv 75 (by norm_num)
  · rw [gv_eq_T 203 (by norm_num)]
    exact DnBv 75 (by norm_num)

theorem bnd_204 : Gv 204 = -2239251068 ∧ LOG1E13LB ≤ gv 204 := by
  constructor
  · rw [Gv_eq_T 204 (by norm_num)]
    exact EqBv 76 (by norm_num)
  · rw [gv_eq_T 204 (by norm_num)]
    exact DnBv 76 (by norm_num)

theorem bnd_205 : Gv 205 = -2054378222 ∧ LOG1E13LB ≤ gv 205 := by
  constructor
  · rw [Gv_eq_T 205 (by norm_num)]
    exact EqBv 77 (by norm_num)
  · rw [gv_eq_T 205 (by norm_num)]
    exact DnBv 77 (by norm_num)

theorem bnd_206 : Gv 206 = -1859758570 ∧ LOG1E13LB ≤ gv 206 := by
  constructor
  · rw [Gv_eq_T 206 (by norm_num)]
    exact EqBv 78 (by norm_num)
  · rw [gv_eq_T 206 (by norm_num)]
    exact DnBv 78 (by norm_num)

theorem bnd_207 : Gv 207 = -1657225336 ∧ LOG1E13LB ≤ gv 207 := by
  constructor
  · rw [Gv_eq_T 207 (by norm_num)]
    exact EqBv 79 (by norm_num)
  · rw [gv_eq_T 207 (by norm_num)]
    exact DnBv 79 (by norm_num)

theorem bnd_208 : Gv 208 = -1448629964 ∧ LOG1E13LB ≤ gv 208 := by
  constructor
  · rw [Gv_eq_T 208 (by norm_num)]
    exact EqBv 80 (by norm_num)
  · rw [gv_eq_T 208 (by norm_num)]
    exact DnBv 80 (by norm_num)

theorem bnd_209 : Gv 209 = -1235725058 ∧ LOG1E13LB ≤ gv 209 := by
  constructor
  · rw [Gv_eq_T 209 (by norm_num)]
    exact EqBv 81 (by norm_num)
  · rw [gv_eq_T 209 (by norm_num)]
    exact DnBv 81 (by norm_num)

theorem bnd_210 : Gv 210 = -1020290000 ∧ LOG1E13LB ≤ gv 210 := by
  constructor
  · rw [Gv_eq_T 210 (by norm_num)]
    exact EqBv 82 (by norm_num)
  · rw [gv_eq_T 210 (by norm_num)]
    exact DnBv 82 (by norm_num)

theorem bnd_211 : Gv 211 = -804018980 ∧ LOG1E13LB ≤ gv 211 := by
  constructor
  · rw [Gv_eq_T 211 (by norm_num)]
    exact EqBv 83 (by norm_num)
  · rw [gv_eq_T 211 (by norm_num)]
    exact DnBv 83 (by norm_num)

theorem bnd_212 : Gv 212 = -588532456 ∧ LOG1E13LB ≤ gv 212 := by
  constructor
  · rw [Gv_eq_T 212 (by norm_num)]
    exact EqBv 84 (by norm_num)
  · rw [gv_eq_T 212 (by norm_num)]
    exact DnBv 84 (by norm_num)

theorem bnd_213 : Gv 213 = -375404078 ∧ LOG1E13LB ≤ gv 213 := by
  constructor
  · rw [Gv_eq_T 213 (by norm_num)]
    exact EqBv 85 (by norm_num)
  · rw [gv_eq_T 213 (by norm_num)]
    exact DnBv 85 (by norm_num)

theorem bnd_214 : Gv 214 = -166147088 ∧ LOG1E13LB ≤ gv 214 := by
  constructor
  · rw [Gv_eq_T 214 (by norm_num)]
    exact EqBv 86 (by norm_num)
  · rw [gv_eq_T 214 (by norm_num)]
    exact DnBv 86 (by norm_num)

theorem bnd_215 : Gv 215 = 37813080 ∧ LOG1E13LB ≤ gv 215 := by
  constructor
  · rw [Gv_eq_T 215 (by norm_num)]
    exact EqBv 87 (by norm_num)
  · rw [gv_eq_T 215 (by norm_num)]
    exact DnBv 87 (by norm_num)

theorem bnd_216 : Gv 216 = 235116532 ∧ LOG1E13LB ≤ gv 216 := by
  constructor
  · rw [Gv_eq_T 216 (by norm_num)]
    exact EqBv 88 (by norm_num)
  · rw [gv_eq_T 216 (by norm_num)]
    exact DnBv 88 (by norm_num)

theorem bnd_217 : Gv 217 = 424419360 ∧ LOG1E13LB ≤ gv 217 := by
  constructor
  · rw [Gv_eq_T 217 (by norm_num)]
    exact EqBv 89 (by norm_num)
  · rw [gv_eq_T 217 (by norm_num)]
    exact DnBv 89 (by norm_num)

theorem bnd_218 : Gv 218 = 604548278 ∧ LOG1E13LB ≤ gv 218 := by
  constructor
  · rw [Gv_eq_T 218 (by norm_num)]
    exact EqBv 90 (by norm_num)
  · rw [gv_eq_T 218 (by norm_num)]
    exact DnBv 90 (by norm_num)

theorem bnd_219 : Gv 219 = 774379946 ∧ LOG1E13LB ≤ gv 219 := by
  constructor
  · rw [Gv_eq_T 219 (by norm_num)]
    exact EqBv 91 (by norm_num)
  · rw [gv_eq_T 219 (by norm_num)]
    exact DnBv 91 (by norm_num)

theorem bnd_220 : Gv 220 = 932822368 ∧ LOG1E13LB ≤ gv 220 := by
  constructor
  · rw [Gv_eq_T 220 (by norm_num)]
    exact EqBv 92 (by norm_num)
  · rw [gv_eq_T 220 (by norm_num)]
    exact DnBv 92 (by norm_num)

theorem bnd_221 : Gv 221 = 1079079026 ∧ LOG1E13LB ≤ gv 221 := by
  constructor
  · rw [Gv_eq_T 221 (by norm_num)]
    exact EqBv 93 (by norm_num)
  · rw [gv_eq_T 221 (by norm_num)]
    exact DnBv 93 (by norm_num)

theorem bnd_222 : Gv 222 = 1212407918 ∧ LOG1E13LB ≤ gv 222 := by
  constructor
  · rw [Gv_eq_T 222 (by norm_num)]
    exact EqBv 94 (by norm_num)
  · rw [gv_eq_T 222 (by norm_num)]
    exact DnBv 94 (by norm_num)

theorem bnd_223 : Gv 223 = 1332337508 ∧ LOG1E13LB ≤ gv 223 := by
  constructor
  · rw [Gv_eq_T 223 (by norm_num)]
    exact EqBv 95 (by norm_num)
  · rw [gv_eq_T 223 (by norm_num)]
    exact DnBv 95 (by norm_num)

theorem bnd_224 : Gv 224 = 1438629884 ∧ LOG1E13LB ≤ gv 224 := by
  constructor
  · rw [Gv_eq_T 224 (by norm_num)]
    exact EqBv 96 (by norm_num)
  · rw [gv_eq_T 224 (by norm_num)]
    exact DnBv 96 (by norm_num)

theorem bnd_225 : Gv 225 = 1531385342 ∧ LOG1E13LB ≤ gv 225 := by
  constructor
  · rw [Gv_eq_T 225 (by norm_num)]
    exact EqBv 97 (by norm_num)
  · rw [gv_eq_T 225 (by norm_num)]
    exact DnBv 97 (by norm_num)

theorem bnd_226 : Gv 226 = 1611009406 ∧ LOG1E13LB ≤ gv 226 := by
  constructor
  · rw [Gv_eq_T 226 (by norm_num)]
    exact EqBv 98 (by norm_num)
  · rw [gv_eq_T 226 (by norm_num)]
    exact DnBv 98 (by norm_num)

theorem bnd_227 : Gv 227 = 1678376558 ∧ LOG1E13LB ≤ gv 227 := by
  constructor
  · rw [Gv_eq_T 227 (by norm_num)]
    exact EqBv 99 (by norm_num)
  · rw [gv_eq_T 227 (by norm_num)]
    exact DnBv 99 (by norm_num)

theorem bnd_228 : Gv 228 = 1734808384 ∧ LOG1E13LB ≤ gv 228 := by
  constructor
  · rw [Gv_eq_T 228 (by norm_num)]
    exact EqBv 100 (by norm_num)
  · rw [gv_eq_T 228 (by norm_num)]
    exact DnBv 100 (by norm_num)

theorem bnd_229 : Gv 229 = 1782101992 ∧ LOG1E13LB ≤ gv 229 := by
  constructor
  · rw [Gv_eq_T 229 (by norm_num)]
    exact EqBv 101 (by norm_num)
  · rw [gv_eq_T 229 (by norm_num)]
    exact DnBv 101 (by norm_num)

theorem bnd_230 : Gv 230 = 1822681978 ∧ LOG1E13LB ≤ gv 230 := by
  constructor
  · rw [Gv_eq_T 230 (by norm_num)]
    exact EqBv 102 (by norm_num)
  · rw [gv_eq_T 230 (by norm_num)]
    exact DnBv 102 (by norm_num)

theorem bnd_231 : Gv 231 = 1859581202 ∧ LOG1E13LB ≤ gv 231 := by
  constructor
  · rw [Gv_eq_T 231 (by norm_num)]
    exact EqBv 103 (by norm_num)
  · rw [gv_eq_T 231 (by norm_num)]
    exact DnBv 103 (by norm_num)

theorem bnd_232 : Gv 232 = 1896534188 ∧ LOG1E13LB ≤ gv 232 := by
  constructor
  · rw [Gv_eq_T 232 (by norm_num)]
    exact EqBv 104 (by norm_num)
  · rw [gv_eq_T 232 (by norm_num)]
    exact DnBv 104 (by norm_num)

theorem bnd_233 : Gv 233 = 1938003954 ∧ LOG1E13LB ≤ gv 233 := by
  constructor
  · rw [Gv_eq_T 233 (by norm_num)]
    exact EqBv 105 (by norm_num)
  · rw [gv_eq_T 233 (by norm_num)]
    exact DnBv 105 (by norm_num)

theorem bnd_234 : Gv 234 = 1989203882 ∧ LOG1E13LB ≤ gv 234 := by
  constructor
  · rw [Gv_eq_T 234 (by norm_num)]
    exact EqBv 106 (by norm_num)
  · rw [gv_eq_T 234 (by norm_num)]
    exact DnBv 106 (by norm_num)

theorem bnd_235 : Gv 235 = 2056252530 ∧ LOG1E13LB ≤ gv 235 := by
  constructor
  · rw [Gv_eq_T 235 (by norm_num)]
    exact EqBv 107 (by norm_num)
  · rw [gv_eq_T 235 (by norm_num)]
    exact DnBv 107 (by norm_num)

theorem bnd_236 : Gv 236 = 2146067142 ∧ LOG1E13LB ≤ gv 236 := by
  constructor
  · rw [Gv_eq_T 236 (by norm_num)]
    exact EqBv 108 (by norm_num)
  · rw [gv_eq_T 236 (by norm_num)]
    exact DnBv 108 (by norm_num)

theorem bnd_237 : Gv 237 = 2266593384 ∧ LOG1E13LB ≤ gv 237 := by
  constructor
  · rw [Gv_eq_T 237 (by norm_num)]
    exact EqBv 109 (by norm_num)
  · rw [gv_eq_T 237 (by norm_num)]
    exact DnBv 109 (by norm_num)

theorem bnd_238 : Gv 238 = 2427238962 ∧ LOG1E13LB ≤ gv 238 := by
  constructor
  · rw [Gv_eq_T 238 (by norm_num)]
    exact EqBv 110 (by norm_num)
  · rw [gv_eq_T 238 (by norm_num)]
    exact DnBv 110 (by norm_num)

theorem bnd_239 : Gv 239 = 2639481496 ∧ LOG1E13LB ≤ gv 239 := by
  constructor
  · rw [Gv_eq_T 239 (by norm_num)]
    exact EqBv 111 (by norm_num)
  · rw [gv_eq_T 239 (by norm_num)]
    exact DnBv 111 (by norm_num)

theorem bnd_240 : Gv 240 = 2919325906 ∧ LOG1E13LB ≤ gv 240 := by
  constructor
  · rw [Gv_eq_T 240 (by norm_num)]
    exact EqBv 112 (by norm_num)
  · rw [gv_eq_T 240 (by norm_num)]
    exact DnBv 112 (by norm_num)

theorem bnd_241 : Gv 241 = 3294419364 ∧ LOG1E13LB ≤ gv 241 := by
  constructor
  · rw [Gv_eq_T 241 (by norm_num)]
    exact EqBv 113 (by norm_num)
  · rw [gv_eq_T 241 (by norm_num)]
    exact DnBv 113 (by norm_num)

theorem bnd_242 : Gv 242 = 3829536944 ∧ LOG1E13LB ≤ gv 242 := by
  constructor
  · rw [Gv_eq_T 242 (by norm_num)]
    exact EqBv 114 (by norm_num)
  · rw [gv_eq_T 242 (by norm_num)]
    exact DnBv 114 (by norm_num)

theorem bnd_243 : Gv 243 = 4790205356 ∧ LOG1E13LB ≤ gv 243 := by
  constructor
  · rw [Gv_eq_T 243 (by norm_num)]
    exact EqBv 115 (by norm_num)
  · rw [gv_eq_T 243 (by norm_num)]
    exact DnBv 115 (by norm_num)

theorem bnd_244 : Gv 244 = 8234477676 ∧ LOG1E13LB ≤ gv 244 := by
  constructor
  · rw [Gv_eq_T 244 (by norm_num)]
    exact EqBv 116 (by norm_num)
  · rw [gv_eq_T 244 (by norm_num)]
    exact DnBv 116 (by norm_num)

theorem bnd_245 : Gv 245 = 8701607684 ∧ LOG1E13LB ≤ gv 245 := by
  constructor
  · rw [Gv_eq_T 245 (by norm_num)]
    exact EqBv 117 (by norm_num)
  · rw [gv_eq_T 245 (by norm_num)]
    exact DnBv 117 (by norm_num)

theorem bnd_246 : Gv 246 = 8209767840 ∧ LOG1E13LB ≤ gv 246 := by
  constructor
  · rw [Gv_eq_T 246 (by norm_num)]
    exact EqBv 118 (by norm_num)
  · rw [gv_eq_T 246 (by norm_num)]
    exact DnBv 118 (by norm_num)

theorem bnd_247 : Gv 247 = 8354693864 ∧ LOG1E13LB ≤ gv 247 := by
  constructor
  · rw [Gv_eq_T 247 (by norm_num)]
    exact EqBv 119 (by norm_num)
  · rw [gv_eq_T 247 (by norm_num)]
    exact DnBv 119 (by norm_num)

theorem bnd_248 : Gv 248 = 8569506500 ∧ LOG1E13LB ≤ gv 248 := by
  constructor
  · rw [Gv_eq_T 248 (by norm_num)]
    exact EqBv 120 (by norm_num)
  · rw [gv_eq_T 248 (by norm_num)]
    exact DnBv 120 (by norm_num)

theorem bnd_249 : Gv 249 = 8787877218 ∧ LOG1E13LB ≤ gv 249 := by
  constructor
  · rw [Gv_eq_T 249 (by norm_num)]
    exact EqBv 121 (by norm_num)
  · rw [gv_eq_T 249 (by norm_num)]
    exact DnBv 121 (by norm_num)

theorem bnd_250 : Gv 250 = 8995817670 ∧ LOG1E13LB ≤ gv 250 := by
  constructor
  · rw [Gv_eq_T 250 (by norm_num)]
    exact EqBv 122 (by norm_num)
  · rw [gv_eq_T 250 (by norm_num)]
    exact DnBv 122 (by norm_num)

theorem bnd_251 : Gv 251 = 9190474524 ∧ LOG1E13LB ≤ gv 251 := by
  constructor
  · rw [Gv_eq_T 251 (by norm_num)]
    exact EqBv 123 (by norm_num)
  · rw [gv_eq_T 251 (by norm_num)]
    exact DnBv 123 (by norm_num)

theorem bnd_252 : Gv 252 = 9371948432 ∧ LOG1E13LB ≤ gv 252 := by
  constructor
  · rw [Gv_eq_T 252 (by norm_num)]
    exact EqBv 124 (by norm_num)
  · rw [gv_eq_T 252 (by norm_num)]
    exact DnBv 124 (by norm_num)

theorem bnd_253 : Gv 253 = 9541267112 ∧ LOG1E13LB ≤ gv 253 := by
  constructor
  · rw [Gv_eq_T 253 (by norm_num)]
    exact EqBv 125 (by norm_num)
  · rw [gv_eq_T 253 (by norm_num)]
    exact DnBv 125 (by norm_num)

theorem bnd_254 : Gv 254 = 9699599376 ∧ LOG1E13LB ≤ gv 254 := by
  constructor
  · rw [Gv_eq_T 254 (by norm_num)]
    exact EqBv 126 (by norm_num)
  · rw [gv_eq_T 254 (by norm_num)]
    exact DnBv 126 (by norm_num)

theorem bnd_255 : Gv 255 = 9847944838 ∧ LOG1E13LB ≤ gv 255 := by
  constructor
  · rw [Gv_eq_T 255 (by norm_num)]
    exact EqBv 127 (by norm_num)
  · rw [gv_eq_T 255 (by norm_num)]
    exact DnBv 127 (by norm_num)

theorem bnd_256 : Gv 256 = 9987634352 ∧ LOG1E13LB ≤ gv 256 := by
  constructor
  · rw [Gv_eq_T 256 (by norm_num)]
    exact EqCv 0 (by norm_num)
  · rw [gv_eq_T 256 (by norm_num)]
    exact DnCv 0 (by norm_num)

theorem bnd_257 : Gv 257 = 10119212792 ∧ LOG1E13LB ≤ gv 257 := by
  constructor
  · rw [Gv_eq_T 257 (by norm_num)]
    exact EqCv 1 (by norm_num)
  · rw [gv_eq_T 257 (by norm_num)]
    exact DnCv 1 (by norm_num)

theorem bnd_258 : Gv 258 = 10243578246 ∧ LOG1E13LB ≤ gv 258 := by
  constructor
  · rw [Gv_eq_T 258 (by norm_num)]
    exact EqCv 2 (by norm_num)
  · rw [gv_eq_T 258 (by norm_num)]
    exact DnCv 2 (by norm_num)

theorem bnd_259 : Gv 259 = 10361415144 ∧ LOG1E13LB ≤ gv 259 := by
  constructor
  · rw [Gv_eq_T 259 (by norm_num)]
    exact EqCv 3 (by norm_num)
  · rw [gv_eq_T 259 (by norm_num)]
    exact DnCv 3 (by norm_num)

theorem bnd_260 : Gv 260 = 10473303134 ∧ LOG1E13LB ≤ gv 260 := by
  constructor
  · rw [Gv_eq_T 260 (by norm_num)]
    exact EqCv 4 (by norm_num)
  · rw [gv_eq_T 260 (by norm_num)]
    exact DnCv 4 (by norm_num)

theorem bnd_261 : Gv 261 = 10579737726 ∧ LOG1E13LB ≤ gv 261 := by
  constructor
  · rw [Gv_eq_T 261 (by norm_num)]
    exact EqCv 5 (by norm_num)
  · rw [gv_eq_T 261 (by norm_num)]
    exact DnCv 5 (by norm_num)

theorem bnd_262 : Gv 262 = 10681195374 ∧ LOG1E13LB ≤ gv 262 := by
  constructor
  · rw [Gv_eq_T 262 (by norm_num)]
    exact EqCv 6 (by norm_num)
  · rw [gv_eq_T 262 (by norm_num)]
    exact DnCv 6 (by norm_num)

theorem bnd_263 : Gv 263 = 10778060700 ∧ LOG1E13LB ≤ gv 263 := by
  constructor
  · rw [Gv_eq_T 263 (by norm_num)]
    exact EqCv 7 (by norm_num)
  · rw [gv_eq_T 263 (by norm_num)]
    exact DnCv 7 (by norm_num)

theorem bnd_264 : Gv 264 = 10870684476 ∧ LOG1E13LB ≤ gv 264 := by
  constructor
  · rw [Gv_eq_T 264 (by norm_num)]
    exact EqCv 8 (by norm_num)
  · rw [gv_eq_T 264 (by norm_num)]
    exact DnCv 8 (by norm_num)

theorem bnd_265 : Gv 265 = 10959389664 ∧ LOG1E13LB ≤ gv 265 := by
  constructor
  · rw [Gv_eq_T 265 (by norm_num)]
    exact EqCv 9 (by norm_num)
  · rw [gv_eq_T 265 (by norm_num)]
    exact DnCv 9 (by norm_num)

theorem bnd_266 : Gv 266 = 11044448672 ∧ LOG1E13LB ≤ gv 266 := by
  constructor
  · rw [Gv_eq_T 266 (by norm_num)]
    exact EqCv 10 (by norm_num)
  · rw [gv_eq_T 266 (by norm_num)]
    exact DnCv 10 (by norm_num)

theorem bnd_267 : Gv 267 = 11126105374 ∧ LOG1E13LB ≤ gv 267 := by
  constructor
  · rw [Gv_eq_T 267 (by norm_num)]
    exact EqCv 11 (by norm_num)
  · rw [gv_eq_T 267 (by norm_num)]
    exact DnCv 11 (by norm_num)

theorem bnd_268 : Gv 268 = 11204592446 ∧ LOG1E13LB ≤ gv 268 := by
  constructor
  · rw [Gv_eq_T 268 (by norm_num)]
    exact EqCv 12 (by norm_num)
  · rw [gv_eq_T 268 (by norm_num)]
    exact DnCv 12 (by norm_num)

theorem bnd_269 : Gv 269 = 11280120200 ∧ LOG1E13LB ≤ gv 269 := by
  constructor
  · rw [Gv_eq_T 269 (by norm_num)]
    exact EqCv 13 (by norm_num)
  · rw [gv_eq_T 269 (by norm_num)]
    exact DnCv 13 (by norm_num)

theorem bnd_270 : Gv 270 = 11352864793 ∧ LOG1E13LB ≤ gv 270 := by
  constructor
  · rw [Gv_eq_T 270 (by norm_num)]
    exact EqCv 14 (by norm_num)
  · rw [gv_eq_T 270 (by norm_num)]
    exact DnCv 14 (by norm_num)

theorem bnd_271 : Gv 271 = 11423001773 ∧ LOG1E13LB ≤ gv 271 := by
  constructor
  · rw [Gv_eq_T 271 (by norm_num)]
    exact EqCv 15 (by norm_num)
  · rw [gv_eq_T 271 (by norm_num)]
    exact DnCv 15 (by norm_num)

theorem bnd_272 : Gv 272 = 11490672477 ∧ LOG1E13LB ≤ gv 272 := by
  constructor
  · rw [Gv_eq_T 272 (by norm_num)]
    exact EqCv 16 (by norm_num)
  · rw [gv_eq_T 272 (by norm_num)]
    exact DnCv 16 (by norm_num)

theorem bnd_273 : Gv 273 = 11556023107 ∧ LOG1E13LB ≤ gv 273 := by
  constructor
  · rw [Gv_eq_T 273 (by norm_num)]
    exact EqCv 17 (by norm_num)
  · rw [gv_eq_T 273 (by norm_num)]
    exact DnCv 17 (by norm_num)

theorem bnd_274 : Gv 274 = 11619176265 ∧ LOG1E13LB ≤ gv 274 := by
  constructor
  · rw [Gv_eq_T 274 (by norm_num)]
    exact EqCv 18 (by norm_num)
  · rw [gv_eq_T 274 (by norm_num)]
    exact DnCv 18 (by norm_num)

theorem bnd_275 : Gv 275 = 11680267589 ∧ LOG1E13LB ≤ gv 275 := by
  constructor
  · rw [Gv_eq_T 275 (by norm_num)]
    exact EqCv 19 (by norm_num)
  · rw [gv_eq_T 275 (by norm_num)]
    exact DnCv 19 (by norm_num)

theorem bnd_276 : Gv 276 = 11739379935 ∧ LOG1E13LB ≤ gv 276 := by
  constructor
  · rw [Gv_eq_T 276 (by norm_num)]
    exact EqCv 20 (by norm_num)
  · rw [gv_eq_T 276 (by norm_num)]
    exact DnCv 20 (by norm_num)

theorem bnd_277 : Gv 277 = 11796649911 ∧ LOG1E13LB ≤ gv 277 := by
  constructor
  · rw [Gv_eq_T 277 (by norm_num)]
    exact EqCv 21 (by norm_num)
  · rw [gv_eq_T 277 (by norm_num)]
    exact DnCv 21 (by norm_num)

theorem bnd_278 : Gv 278 = 11852140745 ∧ LOG1E13LB ≤ gv 278 := by
  constructor
  · rw [Gv_eq_T 278 (by norm_num)]
    exact EqCv 22 (by norm_num)
  · rw [gv_eq_T 278 (by norm_num)]
    exact DnCv 22 (by norm_num)

theorem bnd_279 : Gv 279 = 11905950183 ∧ LOG1E13LB ≤ gv 279 := by
  constructor
  · rw [Gv_eq_T 279 (by norm_num)]
    exact EqCv 23 (by norm_num)
  · rw [gv_eq_T 279 (by norm_num)]
    exact DnCv 23 (by norm_num)

theorem bnd_280 : Gv 280 = 11958150105 ∧ LOG1E13LB ≤ gv 280 := by
  constructor
  · rw [Gv_eq_T 280 (by norm_num)]
    exact EqCv 24 (by norm_num)
  · rw [gv_eq_T 280 (by norm_num)]
    exact DnCv 24 (by norm_num)

theorem bnd_281 : Gv 281 = 12008827613 ∧ LOG1E13LB ≤ gv 281 := by
  constructor
  · rw [Gv_eq_T 281 (by norm_num)]
    exact EqCv 25 (by norm_num)
  · rw [gv_eq_T 281 (by norm_num)]
    exact DnCv 25 (by norm_num)

theorem bnd_282 : Gv 282 = 12058049301 ∧ LOG1E13LB ≤ gv 282 := by
  constructor
  · rw [Gv_eq_T 282 (by norm_num)]
    exact EqCv 26 (by norm_num)
  · rw [gv_eq_T 282 (by norm_num)]
    exact DnCv 26 (by norm_num)

theorem bnd_283 : Gv 283 = 12105868905 ∧ LOG1E13LB ≤ gv 283 := by
  constructor
  · rw [Gv_eq_T 283 (by norm_num)]
    exact EqCv 27 (by norm_num)
  · rw [gv_eq_T 283 (by norm_num)]
    exact DnCv 27 (by norm_num)

theorem bnd_284 : Gv 284 = 12152355281 ∧ LOG1E13LB ≤ gv 284 := by
  constructor
  · rw [Gv_eq_T 284 (by norm_num)]
    exact EqCv 28 (by norm_num)
  · rw [gv_eq_T 284 (by norm_num)]
    exact DnCv 28 (by norm_num)

theorem bnd_285 : Gv 285 = 12197585463 ∧ LOG1E13LB ≤ gv 285 := by
  constructor
  · rw [Gv_eq_T 285 (by norm_num)]
    exact EqCv 29 (by norm_num)
  · rw [gv_eq_T 285 (by norm_num)]
    exact DnCv 29 (by norm_num)

theorem bnd_286 : Gv 286 = 12241576261 ∧ LOG1E13LB ≤ gv 286 := by
  constructor
  · rw [Gv_eq_T 286 (by norm_num)]
    exact EqCv 30 (by norm_num)
  · rw [gv_eq_T 286 (by norm_num)]
    exact DnCv 30 (by norm_num)

theorem bnd_287 : Gv 287 = 12284397213 ∧ LOG1E13LB ≤ gv 287 := by
  constructor
  · rw [Gv_eq_T 287 (by norm_num)]
    exact EqCv 31 (by norm_num)
  · rw [gv_eq_T 287 (by norm_num)]
    exact DnCv 31 (by norm_num)

theorem bnd_288 : Gv 288 = 12326102037 ∧ LOG1E13LB ≤ gv 288 := by
  constructor
  · rw [Gv_eq_T 288 (by norm_num)]
    exact EqCv 32 (by norm_num)
  · rw [gv_eq_T 288 (by norm_num)]
    exact DnCv 32 (by norm_num)

theorem bnd_289 : Gv 289 = 12366719497 ∧ LOG1E13LB ≤ gv 289 := by
  constructor
  · rw [Gv_eq_T 289 (by norm_num)]
    exact EqCv 33 (by norm_num)
  · rw [gv_eq_T 289 (by norm_num)]
    exact DnCv 33 (by norm_num)

theorem bnd_290 : Gv 290 = 12406310503 ∧ LOG1E13LB ≤ gv 290 := by
  constructor
  · rw [Gv_eq_T 290 (by norm_num)]
    exact EqCv 34 (by norm_num)
  · rw [gv_eq_T 290 (by norm_num)]
    exact DnCv 34 (by norm_num)

theorem bnd_291 : Gv 291 = 12444893245 ∧ LOG1E13LB ≤ gv 291 := by
  constructor
  · rw [Gv_eq_T 291 (by norm_num)]
    exact EqCv 35 (by norm_num)
  · rw [gv_eq_T 291 (by norm_num)]
    exact DnCv 35 (by norm_num)

theorem bnd_292 : Gv 292 = 12482526323 ∧ LOG1E13LB ≤ gv 292 := by
  constructor
  · rw [Gv_eq_T 292 (by norm_num)]
    exact EqCv 36 (by norm_num)
  · rw [gv_eq_T 292 (by norm_num)]
    exact DnCv 36 (by norm_num)

theorem bnd_293 : Gv 293 = 12519229429 ∧ LOG1E13LB ≤ gv 293 := by
  constructor
  · rw [Gv_eq_T 293 (by norm_num)]
    exact EqCv 37 (by norm_num)
  · rw [gv_eq_T 293 (by norm_num)]
    exact DnCv 37 (by norm_num)

theorem bnd_294 : Gv 294 = 12555046981 ∧ LOG1E13LB ≤ gv 294 := by
  constructor
  · rw [Gv_eq_T 294 (by norm_num)]
    exact EqCv 38 (by norm_num)
  · rw [gv_eq_T 294 (by norm_num)]
    exact DnCv 38 (by norm_num)

theorem bnd_295 : Gv 295 = 12590010023 ∧ LOG1E13LB ≤ gv 295 := by
  constructor
  · rw [Gv_eq_T 295 (by norm_num)]
    exact EqCv 39 (by norm_num)
  · rw [gv_eq_T 295 (by norm_num)]
    exact DnCv 39 (by norm_num)

theorem bnd_296 : Gv 296 = 12624140521 ∧ LOG1E13LB ≤ gv 296 := by
  constructor
  · rw [Gv_eq_T 296 (by norm_num)]
    exact EqCv 40 (by norm_num)
  · rw [gv_eq_T 296 (by norm_num)]
    exact DnCv 40 (by norm_num)

theorem bnd_297 : Gv 297 = 12657466553 ∧ LOG1E13LB ≤ gv 297 := by
  constructor
  · rw [Gv_eq_T 297 (by norm_num)]
    exact EqCv 41 (by norm_num)
  · rw [gv_eq_T 297 (by norm_num)]
    exact DnCv 41 (by norm_num)

theorem bnd_298 : Gv 298 = 12690028927 ∧ LOG1E13LB ≤ gv 298 := by
  constructor
  · rw [Gv_eq_T 298 (by norm_num)]
    exact EqCv 42 (by norm_num)
  · rw [gv_eq_T 298 (by norm_num)]
    exact DnCv 42 (by norm_num)

theorem bnd_299 : Gv 299 = 12721846253 ∧ LOG1E13LB ≤ gv 299 := by
  constructor
  · rw [Gv_eq_T 299 (by norm_num)]
    exact EqCv 43 (by norm_num)
  · rw [gv_eq_T 299 (by norm_num)]
    exact DnCv 43 (by norm_num)

theorem bnd_300 : Gv 300 = 12752943265 ∧ LOG1E13LB ≤ gv 300 := by
  constructor
  · rw [Gv_eq_T 300 (by norm_num)]
    exact EqCv 44 (by norm_num)
  · rw [gv_eq_T 300 (by norm_num)]
    exact DnCv 44 (by norm_num)

theorem bnd_301 : Gv 301 = 12783338233 ∧ LOG1E13LB ≤ gv 301 := by
  constructor
  · rw [Gv_eq_T 301 (by norm_num)]
    exact EqCv 45 (by norm_num)
  · rw [gv_eq_T 301 (by norm_num)]
    exact DnCv 45 (by norm_num)

theorem bnd_302 : Gv 302 = 12813066525 ∧ LOG1E13LB ≤ gv 302 := by
  constructor
  · rw [Gv_eq_T 302 (by norm_num)]
    exact EqCv 46 (by norm_num)
  · rw [gv_eq_T 302 (by norm_num)]
    exact DnCv 46 (by norm_num)

theorem bnd_303 : Gv 303 = 12842139065 ∧ LOG1E13LB ≤ gv 303 := by
  constructor
  · rw [Gv_eq_T 303 (by norm_num)]
    exact EqCv 47 (by norm_num)
  · rw [gv_eq_T 303 (by norm_num)]
    exact DnCv 47 (by norm_num)

theorem bnd_304 : Gv 304 = 12870580267 ∧ LOG1E13LB ≤ gv 304 := by
  constructor
  · rw [Gv_eq_T 304 (by norm_num)]
    exact EqCv 48 (by norm_num)
  · rw [gv_eq_T 304 (by norm_num)]
    exact DnCv 48 (by norm_num)

theorem bnd_305 : Gv 305 = 12898409753 ∧ LOG1E13LB ≤ gv 305 := by
  constructor
  · rw [Gv_eq_T 305 (by norm_num)]
    exact EqCv 49 (by norm_num)
  · rw [gv_eq_T 305 (by norm_num)]
    exact DnCv 49 (by norm_num)

theorem bnd_306 : Gv 306 = 12925644991 ∧ LOG1E13LB ≤ gv 306 := by
  constructor
  · rw [Gv_eq_T 306 (by norm_num)]
    exact EqCv 50 (by norm_num)
  · rw [gv_eq_T 306 (by norm_num)]
    exact DnCv 50 (by norm_num)

theorem bnd_307 : Gv 307 = 12952299921 ∧ LOG1E13LB ≤ gv 307 := by
  constructor
  · rw [Gv_eq_T 307 (by norm_num)]
    exact EqCv 51 (by norm_num)
  · rw [gv_eq_T 307 (by norm_num)]
    exact DnCv 51 (by norm_num)

theorem bnd_308 : Gv 308 = 12978407497 ∧ LOG1E13LB ≤ gv 308 := by
  constructor
  · rw [Gv_eq_T 308 (by norm_num)]
    exact EqCv 52 (by norm_num)
  · rw [gv_eq_T 308 (by norm_num)]
    exact DnCv 52 (by norm_num)

theorem bnd_309 : Gv 309 = 13003966357 ∧ LOG1E13LB ≤ gv 309 := by
  constructor
  · rw [Gv_eq_T 309 (by norm_num)]
    exact EqCv 53 (by norm_num)
  · rw [gv_eq_T 309 (by norm_num)]
    exact DnCv 53 (by norm_num)

theorem bnd_310 : Gv 310 = 13029004545 ∧ LOG1E13LB ≤ gv 310 := by
  constructor
  · rw [Gv_eq_T 310 (by norm_num)]
    exact EqCv 54 (by norm_num)
  · rw [gv_eq_T 310 (by norm_num)]
    exact DnCv 54 (by norm_num)

theorem bnd_311 : Gv 311 = 13053530831 ∧ LOG1E13LB ≤ gv 311 := by
  constructor
  · rw [Gv_eq_T 311 (by norm_num)]
    exact EqCv 55 (by norm_num)
  · rw [gv_eq_T 311 (by norm_num)]
    exact DnCv 55 (by norm_num)

theorem bnd_312 : Gv 312 = 13077554437 ∧ LOG1E13LB ≤ gv 312 := by
  constructor
  · rw [Gv_eq_T 312 (by norm_num)]
    exact EqCv 56 (by norm_num)
  · rw [gv_eq_T 312 (by norm_num)]
    exact DnCv 56 (by norm_num)

theorem bnd_313 : Gv 313 = 13101104909 ∧ LOG1E13LB ≤ gv 313 := by
  constructor
  · rw [Gv_eq_T 313 (by norm_num)]
    exact EqCv 57 (by norm_num)
  · rw [gv_eq_T 313 (by norm_num)]
    exact DnCv 57 (by norm_num)

theorem bnd_314 : Gv 314 = 13124180329 ∧ LOG1E13LB ≤ gv 314 := by
  constructor
  · rw [Gv_eq_T 314 (by norm_num)]
    exact EqCv 58 (by norm_num)
  · rw [gv_eq_T 314 (by norm_num)]
    exact DnCv 58 (by norm_num)

theorem bnd_315 : Gv 315 = 13146811603 ∧ LOG1E13LB ≤ gv 315 := by
  constructor
  · rw [Gv_eq_T 315 (by norm_num)]
    exact EqCv 59 (by norm_num)
  · rw [gv_eq_T 315 (by norm_num)]
    exact DnCv 59 (by norm_num)

theorem bnd_316 : Gv 316 = 13168983351 ∧ LOG1E13LB ≤ gv 316 := by
  constructor
  · rw [Gv_eq_T 316 (by norm_num)]
    exact EqCv 60 (by norm_num)
  · rw [gv_eq_T 316 (by norm_num)]
    exact DnCv 60 (by norm_num)

theorem bnd_317 : Gv 317 = 13190736745 ∧ LOG1E13LB ≤ gv 317 := by
  constructor
  · rw [Gv_eq_T 317 (by norm_num)]
    exact EqCv 61 (by norm_num)
  · rw [gv_eq_T 317 (by norm_num)]
    exact DnCv 61 (by norm_num)

theorem bnd_318 : Gv 318 = 13212066335 ∧ LOG1E13LB ≤ gv 318 := by
  constructor
  · rw [Gv_eq_T 318 (by norm_num)]
    exact EqCv 62 (by norm_num)
  · rw [gv_eq_T 318 (by norm_num)]
    exact DnCv 62 (by norm_num)

theorem bnd_319 : Gv 319 = 13232991669 ∧ LOG1E13LB ≤ gv 319 := by
  constructor
  · rw [Gv_eq_T 319 (by norm_num)]
    exact EqCv 63 (by norm_num)
  · rw [gv_eq_T 319 (by norm_num)]
    exact DnCv 63 (by norm_num)

theorem bnd_320 : Gv 320 = 13253510105 ∧ LOG1E13LB ≤ gv 320 := by
  constructor
  · rw [Gv_eq_T 320 (by norm_num)]
    exact EqCv 64 (by norm_num)
  · rw [gv_eq_T 320 (by norm_num)]
    exact DnCv 64 (by norm_num)

theorem bnd_321 : Gv 321 = 13273646667 ∧ LOG1E13LB ≤ gv 321 := by
  constructor
  · rw [Gv_eq_T 321 (by norm_num)]
    exact EqCv 65 (by norm_num)
  · rw [gv_eq_T 321 (by norm_num)]
    exact DnCv 65 (by norm_num)

theorem bnd_322 : Gv 322 = 13293405841 ∧ LOG1E13LB ≤ gv 322 := by
  constructor
  · rw [Gv_eq_T 322 (by norm_num)]
    exact EqCv 66 (by norm_num)
  · rw [gv_eq_T 322 (by norm_num)]
    exact DnCv 66 (by norm_num)

theorem bnd_323 : Gv 323 = 13312797303 ∧ LOG1E13LB ≤ gv 323 := by
  constructor
  · rw [Gv_eq_T 323 (by norm_num)]
    exact EqCv 67 (by norm_num)
  · rw [gv_eq_T 323 (by norm_num)]
    exact DnCv 67 (by norm_num)

theorem bnd_324 : Gv 324 = 13331828785 ∧ LOG1E13LB ≤ gv 324 := by
  constructor
  · rw [Gv_eq_T 324 (by norm_num)]
    exact EqCv 68 (by norm_num)
  · rw [gv_eq_T 324 (by norm_num)]
    exact DnCv 68 (by norm_num)

theorem bnd_325 : Gv 325 = 13350504645 ∧ LOG1E13LB ≤ gv 325 := by
  constructor
  · rw [Gv_eq_T 325 (by norm_num)]
    exact EqCv 69 (by norm_num)
  · rw [gv_eq_T 325 (by norm_num)]
    exact DnCv 69 (by norm_num)

theorem bnd_326 : Gv 326 = 13368848099 ∧ LOG1E13LB ≤ gv 326 := by
  constructor
  · rw [Gv_eq_T 326 (by norm_num)]
    exact EqCv 70 (by norm_num)
  · rw [gv_eq_T 326 (by norm_num)]
    exact DnCv 70 (by norm_num)

theorem bnd_327 : Gv 327 = 13386855289 ∧ LOG1E13LB ≤ gv 327 := by
  constructor
  · rw [Gv_eq_T 327 (by norm_num)]
    exact EqCv 71 (by norm_num)
  · rw [gv_eq_T 327 (by norm_num)]
    exact DnCv 71 (by norm_num)

theorem bnd_328 : Gv 328 = 13404546333 ∧ LOG1E13LB ≤ gv 328 := by
  constructor
  · rw [Gv_eq_T 328 (by norm_num)]
    exact EqCv 72 (by norm_num)
  · rw [gv_eq_T 328 (by norm_num)]
    exact DnCv 72 (by norm_num)

theorem bnd_329 : Gv 329 = 13421907153 ∧ LOG1E13LB ≤ gv 329 := by
  constructor
  · rw [Gv_eq_T 329 (by norm_num)]
    exact EqCv 73 (by norm_num)
  · rw [gv_eq_T 329 (by norm_num)]
    exact DnCv 73 (by norm_num)

theorem bnd_330 : Gv 330 = 13438968173 ∧ LOG1E13LB ≤ gv 330 := by
  constructor
  · rw [Gv_eq_T 330 (by norm_num)]
    exact EqCv 74 (by norm_num)
  · rw [gv_eq_T 330 (by norm_num)]
    exact DnCv 74 (by norm_num)

theorem bnd_331 : Gv 331 = 13455720625 ∧ LOG1E13LB ≤ gv 331 := by
  constructor
  · rw [Gv_eq_T 331 (by norm_num)]
    exact EqCv 75 (by norm_num)
  · rw [gv_eq_T 331 (by norm_num)]
    exact DnCv 75 (by norm_num)

theorem bnd_332 : Gv 332 = 13472181353 ∧ LOG1E13LB ≤ gv 332 := by
  constructor
  · rw [Gv_eq_T 332 (by norm_num)]
    exact EqCv 76 (by norm_num)
  · rw [gv_eq_T 332 (by norm_num)]
    exact DnCv 76 (by norm_num)

theorem bnd_333 : Gv 333 = 13488353471 ∧ LOG1E13LB ≤ gv 333 := by
  constructor
  · rw [Gv_eq_T 333 (by norm_num)]
    exact EqCv 77 (by norm_num)
  · rw [gv_eq_T 333 (by norm_num)]
    exact DnCv 77 (by norm_num)

theorem bnd_334 : Gv 334 = 13504251737 ∧ LOG1E13LB ≤ gv 334 := by
  constructor
  · rw [Gv_eq_T 334 (by norm_num)]
    exact EqCv 78 (by norm_num)
  · rw [gv_eq_T 334 (by norm_num)]
    exact DnCv 78 (by norm_num)

theorem bnd_335 : Gv 335 = 13519862489 ∧ LOG1E13LB ≤ gv 335 := by
  constructor
  · rw [Gv_eq_T 335 (by norm_num)]
    exact EqCv 79 (by norm_num)
  · rw [gv_eq_T 335 (by norm_num)]
    exact DnCv 79 (by norm_num)

theorem bnd_336 : Gv 336 = 13535208585 ∧ LOG1E13LB ≤ gv 336 := by
  constructor
  · rw [Gv_eq_T 336 (by norm_num)]
    exact EqCv 80 (by norm_num)
  · rw [gv_eq_T 336 (by norm_num)]
    exact DnCv 80 (by norm_num)

theorem bnd_337 : Gv 337 = 13550292701 ∧ LOG1E13LB ≤ gv 337 := by
  constructor
  · rw [Gv_eq_T 337 (by norm_num)]
    exact EqCv 81 (by norm_num)
  · rw [gv_eq_T 337 (by norm_num)]
    exact DnCv 81 (by norm_num)

theorem bnd_338 : Gv 338 = 13565118027 ∧ LOG1E13LB ≤ gv 338 := by
  constructor
  · rw [Gv_eq_T 338 (by norm_num)]
    exact EqCv 82 (by norm_num)
  · rw [gv_eq_T 338 (by norm_num)]
    exact DnCv 82 (by norm_num)

theorem bnd_339 : Gv 339 = 13579694197 ∧ LOG1E13LB ≤ gv 339 := by
  constructor
  · rw [Gv_eq_T 339 (by norm_num)]
    exact EqCv 83 (by norm_num)
  · rw [gv_eq_T 339 (by norm_num)]
    exact DnCv 83 (by norm_num)

theorem bnd_340 : Gv 340 = 13594023283 ∧ LOG1E13LB ≤ gv 340 := by
  constructor
  · rw [Gv_eq_T 340 (by norm_num)]
    exact EqCv 84 (by norm_num)
  · rw [gv_eq_T 340 (by norm_num)]
    exact DnCv 84 (by norm_num)

theorem bnd_341 : Gv 341 = 13608104193 ∧ LOG1E13LB ≤ gv 341 := by
  constructor
  · rw [Gv_eq_T 341 (by norm_num)]
    exact EqCv 85 (by norm_num)
  · rw [gv_eq_T 341 (by norm_num)]
    exact DnCv 85 (by norm_num)

theorem bnd_342 : Gv 342 = 13621956421 ∧ LOG1E13LB ≤ gv 342 := by
  constructor
  · rw [Gv_eq_T 342 (by norm_num)]
    exact EqCv 86 (by norm_num)
  · rw [gv_eq_T 342 (by norm_num)]
    exact DnCv 86 (by norm_num)

theorem bnd_343 : Gv 343 = 13635583067 ∧ LOG1E13LB ≤ gv 343 := by
  constructor
  · rw [Gv_eq_T 343 (by norm_num)]
    exact EqCv 87 (by norm_num)
  · rw [gv_eq_T 343 (by norm_num)]
    exact DnCv 87 (by norm_num)

theorem bnd_344 : Gv 344 = 13648980529 ∧ LOG1E13LB ≤ gv 344 := by
  constructor
  · rw [Gv_eq_T 344 (by norm_num)]
    exact EqCv 88 (by norm_num)
  · rw [gv_eq_T 344 (by norm_num)]
    exact DnCv 88 (by norm_num)

theorem bnd_345 : Gv 345 = 13662152619 ∧ LOG1E13LB ≤ gv 345 := by
  constructor
  · rw [Gv_eq_T 345 (by norm_num)]
    exact EqCv 89 (by norm_num)
  · rw [gv_eq_T 345 (by norm_num)]
    exact DnCv 89 (by norm_num)

theorem bnd_346 : Gv 346 = 13675109375 ∧ LOG1E13LB ≤ gv 346 := by
  constructor
  · rw [Gv_eq_T 346 (by norm_num)]
    exact EqCv 90 (by norm_num)
  · rw [gv_eq_T 346 (by norm_num)]
    exact DnCv 90 (by norm_num)

theorem bnd_347 : Gv 347 = 13687859219 ∧ LOG1E13LB ≤ gv 347 := by
  constructor
  · rw [Gv_eq_T 347 (by norm_num)]
    exact EqCv 91 (by norm_num)
  · rw [gv_eq_T 347 (by norm_num)]
    exact DnCv 91 (by norm_num)

theorem bnd_348 : Gv 348 = 13700394491 ∧ LOG1E13LB ≤ gv 348 := by
  constructor
  · rw [Gv_eq_T 348 (by norm_num)]
    exact EqCv 92 (by norm_num)
  · rw [gv_eq_T 348 (by norm_num)]
    exact DnCv 92 (by norm_num)

theorem bnd_349 : Gv 349 = 13712725715 ∧ LOG1E13LB ≤ gv 349 := by
  constructor
  · rw [Gv_eq_T 349 (by norm_num)]
    exact EqCv 93 (by norm_num)
  · rw [gv_eq_T 349 (by norm_num)]
    exact DnCv 93 (by norm_num)

theorem bnd_350 : Gv 350 = 13724864337 ∧ LOG1E13LB ≤ gv 350 := by
  constructor
  · rw [Gv_eq_T 350 (by norm_num)]
    exact EqCv 94 (by norm_num)
  · rw [gv_eq_T 350 (by norm_num)]
    exact DnCv 94 (by norm_num)

theorem bnd_351 : Gv 351 = 13736804901 ∧ LOG1E13LB ≤ gv 351 := by
  constructor
  · rw [Gv_eq_T 351 (by norm_num)]
    exact EqCv 95 (by norm_num)
  · rw [gv_eq_T 351 (by norm_num)]
    exact DnCv 95 (by norm_num)

theorem bnd_352 : Gv 352 = 13748553765 ∧ LOG1E13LB ≤ gv 352 := by
  constructor
  · rw [Gv_eq_T 352 (by norm_num)]
    exact EqCv 96 (by norm_num)
  · rw [gv_eq_T 352 (by norm_num)]
    exact DnCv 96 (by norm_num)

theorem bnd_353 : Gv 353 = 13760114849 ∧ LOG1E13LB ≤ gv 353 := by
  constructor
  · rw [Gv_eq_T 353 (by norm_num)]
    exact EqCv 97 (by norm_num)
  · rw [gv_eq_T 353 (by norm_num)]
    exact DnCv 97 (by norm_num)

theorem bnd_354 : Gv 354 = 13771487537 ∧ LOG1E13LB ≤ gv 354 := by
  constructor
  · rw [Gv_eq_T 354 (by norm_num)]
    exact EqCv 98 (by norm_num)
  · rw [gv_eq_T 354 (by norm_num)]
    exact DnCv 98 (by norm_num)

theorem bnd_355 : Gv 355 = 13782687043 ∧ LOG1E13LB ≤ gv 355 := by
  constructor
  · rw [Gv_eq_T 355 (by norm_num)]
    exact EqCv 99 (by norm_num)
  · rw [gv_eq_T 355 (by norm_num)]
    exact DnCv 99 (by norm_num)

theorem bnd_356 : Gv 356 = 13793700473 ∧ LOG1E13LB ≤ gv 356 := by
  constructor
  · rw [Gv_eq_T 356 (by norm_num)]
    exact EqCv 100 (by norm_num)
  · rw [gv_eq_T 356 (by norm_num)]
    exact DnCv 100 (by norm_num)

theorem bnd_357 : Gv 357 = 13804551343 ∧ LOG1E13LB ≤ gv 357 := by
  constructor
  · rw [Gv_eq_T 357 (by norm_num)]
    exact EqCv 101 (by norm_num)
  · rw [gv_eq_T 357 (by norm_num)]
    exact DnCv 101 (by norm_num)

theorem bnd_358 : Gv 358 = 13815223239 ∧ LOG1E13LB ≤ gv 358 := by
  constructor
  · rw [Gv_eq_T 358 (by norm_num)]
    exact EqCv 102 (by norm_num)
  · rw [gv_eq_T 358 (by norm_num)]
    exact DnCv 102 (by norm_num)

theorem bnd_359 : Gv 359 = 13825734083 ∧ LOG1E13LB ≤ gv 359 := by
  constructor
  · rw [Gv_eq_T 359 (by norm_num)]
    exact EqCv 103 (by norm_num)
  · rw [gv_eq_T 359 (by norm_num)]
    exact DnCv 103 (by norm_num)

theorem bnd_360 : Gv 360 = 13836077169 ∧ LOG1E13LB ≤ gv 360 := by
  constructor
  · rw [Gv_eq_T 360 (by norm_num)]
    exact EqCv 104 (by norm_num)
  · rw [gv_eq_T 360 (by norm_num)]
    exact DnCv 104 (by norm_num)

theorem bnd_361 : Gv 361 = 13846261005 ∧ LOG1E13LB ≤ gv 361 := by
  constructor
  · rw [Gv_eq_T 361 (by norm_num)]
    exact EqCv 105 (by norm_num)
  · rw [gv_eq_T 361 (by norm_num)]
    exact DnCv 105 (by norm_num)

theorem bnd_362 : Gv 362 = 13856284561 ∧ LOG1E13LB ≤ gv 362 := by
  constructor
  · rw [Gv_eq_T 362 (by norm_num)]
    exact EqCv 106 (by norm_num)
  · rw [gv_eq_T 362 (by norm_num)]
    exact DnCv 106 (by norm_num)

theorem bnd_363 : Gv 363 = 13866153881 ∧ LOG1E13LB ≤ gv 363 := by
  constructor
  · rw [Gv_eq_T 363 (by norm_num)]
    exact EqCv 107 (by norm_num)
  · rw [gv_eq_T 363 (by norm_num)]
    exact DnCv 107 (by norm_num)

theorem bnd_364 : Gv 364 = 13875870943 ∧ LOG1E13LB ≤ gv 364 := by
  constructor
  · rw [Gv_eq_T 364 (by norm_num)]
    exact EqCv 108 (by norm_num)
  · rw [gv_eq_T 364 (by norm_num)]
    exact DnCv 108 (by norm_num)

theorem bnd_365 : Gv 365 = 13885436903 ∧ LOG1E13LB ≤ gv 365 := by
  constructor
  · rw [Gv_eq_T 365 (by norm_num)]
    exact EqCv 109 (by norm_num)
  · rw [gv_eq_T 365 (by norm_num)]
    exact DnCv 109 (by norm_num)

theorem bnd_366 : Gv 366 = 13894860515 ∧ LOG1E13LB ≤ gv 366 := by
  constructor
  · rw [Gv_eq_T 366 (by norm_num)]
    exact EqCv 110 (by norm_num)
  · rw [gv_eq_T 366 (by norm_num)]
    exact DnCv 110 (by norm_num)

theorem bnd_367 : Gv 367 = 13904135469 ∧ LOG1E13LB ≤ gv 367 := by
  constructor
  · rw [Gv_eq_T 367 (by norm_num)]
    exact EqCv 111 (by norm_num)
  · rw [gv_eq_T 367 (by norm_num)]
    exact DnCv 111 (by norm_num)

theorem bnd_368 : Gv 368 = 13913273233 ∧ LOG1E13LB ≤ gv 368 := by
  constructor
  · rw [Gv_eq_T 368 (by norm_num)]
    exact EqCv 112 (by norm_num)
  · rw [gv_eq_T 368 (by norm_num)]
    exact DnCv 112 (by norm_num)

theorem bnd_369 : Gv 369 = 13922264865 ∧ LOG1E13LB ≤ gv 369 := by
  constructor
  · rw [Gv_eq_T 369 (by norm_num)]
    exact EqCv 113 (by norm_num)
  · rw [gv_eq_T 369 (by norm_num)]
    exact DnCv 113 (by norm_num)

theorem bnd_370 : Gv 370 = 13931119277 ∧ LOG1E13LB ≤ gv 370 := by
  constructor
  · rw [Gv_eq_T 370 (by norm_num)]
    exact EqCv 114 (by norm_num)
  · rw [gv_eq_T 370 (by norm_num)]
    exact DnCv 114 (by norm_num)

theorem bnd_371 : Gv 371 = 13939840961 ∧ LOG1E13LB ≤ gv 371 := by
  constructor
  · rw [Gv_eq_T 371 (by norm_num)]
    exact EqCv 115 (by norm_num)
  · rw [gv_eq_T 371 (by norm_num)]
    exact DnCv 115 (by norm_num)

theorem bnd_372 : Gv 372 = 13948436735 ∧ LOG1E13LB ≤ gv 372 := by
  constructor
  · rw [Gv_eq_T 372 (by norm_num)]
    exact EqCv 116 (by norm_num)
  · rw [gv_eq_T 372 (by norm_num)]
    exact DnCv 116 (by norm_num)

theorem bnd_373 : Gv 373 = 13956893285 ∧ LOG1E13LB ≤ gv 373 := by
  constructor
  · rw [Gv_eq_T 373 (by norm_num)]
    exact EqCv 117 (by norm_num)
  · rw [gv_eq_T 373 (by norm_num)]
    exact DnCv 117 (by norm_num)

theorem bnd_374 : Gv 374 = 13965227855 ∧ LOG1E13LB ≤ gv 374 := by
  constructor
  · rw [Gv_eq_T 374 (by norm_num)]
    exact EqCv 118 (by norm_num)
  · rw [gv_eq_T 374 (by norm_num)]
    exact DnCv 118 (by norm_num)

theorem bnd_375 : Gv 375 = 13973438773 ∧ LOG1E13LB ≤ gv 375 := by
  constructor
  · rw [Gv_eq_T 375 (by norm_num)]
    exact EqCv 119 (by norm_num)
  · rw [gv_eq_T 375 (by norm_num)]
    exact DnCv 119 (by norm_num)

theorem bnd_376 : Gv 376 = 13981519411 ∧ LOG1E13LB ≤ gv 376 := by
  constructor
  · rw [Gv_eq_T 376 (by norm_num)]
    exact EqCv 120 (by norm_num)
  · rw [gv_eq_T 376 (by norm_num)]
    exact DnCv 120 (by norm_num)

theorem bnd_377 : Gv 377 = 13989485913 ∧ LOG1E13LB ≤ gv 377 := by
  constructor
  · rw [Gv_eq_T 377 (by norm_num)]
    exact EqCv 121 (by norm_num)
  · rw [gv_eq_T 377 (by norm_num)]
    exact DnCv 121 (by norm_num)

theorem bnd_378 : Gv 378 = 13997328807 ∧ LOG1E13LB ≤ gv 378 := by
  constructor
  · rw [Gv_eq_T 378 (by norm_num)]
    exact EqCv 122 (by norm_num)
  · rw [gv_eq_T 378 (by norm_num)]
    exact DnCv 122 (by norm_num)

theorem bnd_379 : Gv 379 = 14005053127 ∧ LOG1E13LB ≤ gv 379 := by
  constructor
  · rw [Gv_eq_T 379 (by norm_num)]
    exact EqCv 123 (by norm_num)
  · rw [gv_eq_T 379 (by norm_num)]
    exact DnCv 123 (by norm_num)

theorem bnd_380 : Gv 380 = 14012663575 ∧ LOG1E13LB ≤ gv 380 := by
  constructor
  · rw [Gv_eq_T 380 (by norm_num)]
    exact EqCv 124 (by norm_num)
  · rw [gv_eq_T 380 (by norm_num)]
    exact DnCv 124 (by norm_num)

theorem bnd_381 : Gv 381 = 14020159123 ∧ LOG1E13LB ≤ gv 381 := by
  constructor
  · rw [Gv_eq_T 381 (by norm_num)]
    exact EqCv 125 (by norm_num)
  · rw [gv_eq_T 381 (by norm_num)]
    exact DnCv 125 (by norm_num)

theorem bnd_382 : Gv 382 = 14027542251 ∧ LOG1E13LB ≤ gv 382 := by
  constructor
  · rw [Gv_eq_T 382 (by norm_num)]
    exact EqCv 126 (by norm_num)
  · rw [gv_eq_T 382 (by norm_num)]
    exact DnCv 126 (by norm_num)

theorem bnd_383 : Gv 383 = 14034817339 ∧ LOG1E13LB ≤ gv 383 := by
  constructor
  · rw [Gv_eq_T 383 (by norm_num)]
    exact EqCv 127 (by norm_num)
  · rw [gv_eq_T 383 (by norm_num)]
    exact DnCv 127 (by norm_num)

theorem bnd_384 : Gv 384 = 14041982549 ∧ LOG1E13LB ≤ gv 384 := by
  constructor
  · rw [Gv_eq_T 384 (by norm_num)]
    exact EqDv 0 (by norm_num)
  · rw [gv_eq_T 384 (by norm_num)]
    exact DnDv 0 (by norm_num)

theorem bnd_385 : Gv 385 = 14049040545 ∧ LOG1E13LB ≤ gv 385 := by
  constructor
  · rw [Gv_eq_T 385 (by norm_num)]
    exact EqDv 1 (by norm_num)
  · rw [gv_eq_T 385 (by norm_num)]
    exact DnDv 1 (by norm_num)

theorem bnd_386 : Gv 386 = 14055989651 ∧ LOG1E13LB ≤ gv 386 := by
  constructor
  · rw [Gv_eq_T 386 (by norm_num)]
    exact EqDv 2 (by norm_num)
  · rw [gv_eq_T 386 (by norm_num)]
    exact DnDv 2 (by norm_num)

theorem bnd_387 : Gv 387 = 14062846185 ∧ LOG1E13LB ≤ gv 387 := by
  constructor
  · rw [Gv_eq_T 387 (by norm_num)]
    exact EqDv 3 (by norm_num)
  · rw [gv_eq_T 387 (by norm_num)]
    exact DnDv 3 (by norm_num)

theorem bnd_388 : Gv 388 = 14069588837 ∧ LOG1E13LB ≤ gv 388 := by
  constructor
  · rw [Gv_eq_T 388 (by norm_num)]
    exact EqDv 4 (by norm_num)
  · rw [gv_eq_T 388 (by norm_num)]
    exact DnDv 4 (by norm_num)

theorem bnd_389 : Gv 389 = 14076236473 ∧ LOG1E13LB ≤ gv 389 := by
  constructor
  · rw [Gv_eq_T 389 (by norm_num)]
    exact EqDv 5 (by norm_num)
  · rw [gv_eq_T 389 (by norm_num)]
    exact DnDv 5 (by norm_num)

theorem bnd_390 : Gv 390 = 14082783031 ∧ LOG1E13LB ≤ gv 390 := by
  constructor
  · rw [Gv_eq_T 390 (by norm_num)]
    exact EqDv 6 (by norm_num)
  · rw [gv_eq_T 390 (by norm_num)]
    exact DnDv 6 (by norm_num)

theorem bnd_391 : Gv 391 = 14089237669 ∧ LOG1E13LB ≤ gv 391 := by
  constructor
  · rw [Gv_eq_T 391 (by norm_num)]
    exact EqDv 7 (by norm_num)
  · rw [gv_eq_T 391 (by norm_num)]
    exact DnDv 7 (by norm_num)

theorem bnd_392 : Gv 392 = 14095592757 ∧ LOG1E13LB ≤ gv 392 := by
  constructor
  · rw [Gv_eq_T 392 (by norm_num)]
    exact EqDv 8 (by norm_num)
  · rw [gv_eq_T 392 (by norm_num)]
    exact DnDv 8 (by norm_num)

theorem bnd_393 : Gv 393 = 14101852839 ∧ LOG1E13LB ≤ gv 393 := by
  constructor
  · rw [Gv_eq_T 393 (by norm_num)]
    exact EqDv 9 (by norm_num)
  · rw [gv_eq_T 393 (by norm_num)]
    exact DnDv 9 (by norm_num)

theorem bnd_394 : Gv 394 = 14108017185 ∧ LOG1E13LB ≤ gv 394 := by
  constructor
  · rw [Gv_eq_T 394 (by norm_num)]
    exact EqDv 10 (by norm_num)
  · rw [gv_eq_T 394 (by norm_num)]
    exact DnDv 10 (by norm_num)

theorem bnd_395 : Gv 395 = 14114092769 ∧ LOG1E13LB ≤ gv 395 := by
  constructor
  · rw [Gv_eq_T 395 (by norm_num)]
    exact EqDv 11 (by norm_num)
  · rw [gv_eq_T 395 (by norm_num)]
    exact DnDv 11 (by norm_num)

theorem bnd_396 : Gv 396 = 14120077651 ∧ LOG1E13LB ≤ gv 396 := by
  constructor
  · rw [Gv_eq_T 396 (by norm_num)]
    exact EqDv 12 (by norm_num)
  · rw [gv_eq_T 396 (by norm_num)]
    exact DnDv 12 (by norm_num)

theorem bnd_397 : Gv 397 = 14125975623 ∧ LOG1E13LB ≤ gv 397 := by
  constructor
  · rw [Gv_eq_T 397 (by norm_num)]
    exact EqDv 13 (by norm_num)
  · rw [gv_eq_T 397 (by norm_num)]
    exact DnDv 13 (by norm_num)

theorem bnd_398 : Gv 398 = 14131783693 ∧ LOG1E13LB ≤ gv 398 := by
  constructor
  · rw [Gv_eq_T 398 (by norm_num)]
    exact EqDv 14 (by norm_num)
  · rw [gv_eq_T 398 (by norm_num)]
    exact DnDv 14 (by norm_num)

theorem bnd_399 : Gv 399 = 14137501071 ∧ LOG1E13LB ≤ gv 399 := by
  constructor
  · rw [Gv_eq_T 399 (by norm_num)]
    exact EqDv 15 (by norm_num)
  · rw [gv_eq_T 399 (by norm_num)]
    exact DnDv 15 (by norm_num)

theorem bnd_400 : Gv 400 = 14143137469 ∧ LOG1E13LB ≤ gv 400 := by
  constructor
  · rw [Gv_eq_T 400 (by norm_num)]
    exact EqDv 16 (by norm_num)
  · rw [gv_eq_T 400 (by norm_num)]
    exact DnDv 16 (by norm_num)

theorem bnd_401 : Gv 401 = 14148695859 ∧ LOG1E13LB ≤ gv 401 := by
  constructor
  · rw [Gv_eq_T 401 (by norm_num)]
    exact EqDv 17 (by norm_num)
  · rw [gv_eq_T 401 (by norm_num)]
    exact DnDv 17 (by norm_num)

theorem bnd_402 : Gv 402 = 14154159291 ∧ LOG1E13LB ≤ gv 402 := by
  constructor
  · rw [Gv_eq_T 402 (by norm_num)]
    exact EqDv 18 (by norm_num)
  · rw [gv_eq_T 402 (by norm_num)]
    exact DnDv 18 (by norm_num)

theorem bnd_403 : Gv 403 = 14159551895 ∧ LOG1E13LB ≤ gv 403 := by
  constructor
  · rw [Gv_eq_T 403 (by norm_num)]
    exact EqDv 19 (by norm_num)
  · rw [gv_eq_T 403 (by norm_num)]
    exact DnDv 19 (by norm_num)

theorem bnd_404 : Gv 404 = 14164854659 ∧ LOG1E13LB ≤ gv 404 := by
  constructor
  · rw [Gv_eq_T 404 (by norm_num)]
    exact EqDv 20 (by norm_num)
  · rw [gv_eq_T 404 (by norm_num)]
    exact DnDv 20 (by norm_num)

theorem bnd_405 : Gv 405 = 14170081923 ∧ LOG1E13LB ≤ gv 405 := by
  constructor
  · rw [Gv_eq_T 405 (by norm_num)]
    exact EqDv 21 (by norm_num)
  · rw [gv_eq_T 405 (by norm_num)]
    exact DnDv 21 (by norm_num)

theorem bnd_406 : Gv 406 = 14175231817 ∧ LOG1E13LB ≤ gv 406 := by
  constructor
  · rw [Gv_eq_T 406 (by norm_num)]
    exact EqDv 22 (by norm_num)
  · rw [gv_eq_T 406 (by norm_num)]
    exact DnDv 22 (by norm_num)

theorem bnd_407 : Gv 407 = 14180301331 ∧ LOG1E13LB ≤ gv 407 := by
  constructor
  · rw [Gv_eq_T 407 (by norm_num)]
    exact EqDv 23 (by norm_num)
  · rw [gv_eq_T 407 (by norm_num)]
    exact DnDv 23 (by norm_num)

theorem bnd_408 : Gv 408 = 14185296101 ∧ LOG1E13LB ≤ gv 408 := by
  constructor
  · rw [Gv_eq_T 408 (by norm_num)]
    exact EqDv 24 (by norm_num)
  · rw [gv_eq_T 408 (by norm_num)]
    exact DnDv 24 (by norm_num)

theorem bnd_409 : Gv 409 = 14190212263 ∧ LOG1E13LB ≤ gv 409 := by
  constructor
  · rw [Gv_eq_T 409 (by norm_num)]
    exact EqDv 25 (by norm_num)
  · rw [gv_eq_T 409 (by norm_num)]
    exact DnDv 25 (by norm_num)

theorem bnd_410 : Gv 410 = 14195054357 ∧ LOG1E13LB ≤ gv 410 := by
  constructor
  · rw [Gv_eq_T 410 (by norm_num)]
    exact EqDv 26 (by norm_num)
  · rw [gv_eq_T 410 (by norm_num)]
    exact DnDv 26 (by norm_num)

theorem bnd_411 : Gv 411 = 14199825455 ∧ LOG1E13LB ≤ gv 411 := by
  constructor
  · rw [Gv_eq_T 411 (by norm_num)]
    exact EqDv 27 (by norm_num)
  · rw [gv_eq_T 411 (by norm_num)]
    exact DnDv 27 (by norm_num)

theorem bnd_412 : Gv 412 = 14204525339 ∧ LOG1E13LB ≤ gv 412 := by
  constructor
  · rw [Gv_eq_T 412 (by norm_num)]
    exact EqDv 28 (by norm_num)
  · rw [gv_eq_T 412 (by norm_num)]
    exact DnDv 28 (by norm_num)

theorem bnd_413 : Gv 413 = 14209151419 ∧ LOG1E13LB ≤ gv 413 := by
  constructor
  · rw [Gv_eq_T 413 (by norm_num)]
    exact EqDv 29 (by norm_num)
  · rw [gv_eq_T 413 (by norm_num)]
    exact DnDv 29 (by norm_num)

theorem bnd_414 : Gv 414 = 14213703157 ∧ LOG1E13LB ≤ gv 414 := by
  constructor
  · rw [Gv_eq_T 414 (by norm_num)]
    exact EqDv 30 (by norm_num)
  · rw [gv_eq_T 414 (by norm_num)]
    exact DnDv 30 (by norm_num)

theorem bnd_415 : Gv 415 = 14218187417 ∧ LOG1E13LB ≤ gv 415 := by
  constructor
  · rw [Gv_eq_T 415 (by norm_num)]
    exact EqDv 31 (by norm_num)
  · rw [gv_eq_T 415 (by norm_num)]
    exact DnDv 31 (by norm_num)

theorem bnd_416 : Gv 416 = 14222606385 ∧ LOG1E13LB ≤ gv 416 := by
  constructor
  · rw [Gv_eq_T 416 (by norm_num)]
    exact EqDv 32 (by norm_num)
  · rw [gv_eq_T 416 (by norm_num)]
    exact DnDv 32 (by norm_num)

theorem bnd_417 : Gv 417 = 14226950237 ∧ LOG1E13LB ≤ gv 417 := by
  constructor
  · rw [Gv_eq_T 417 (by norm_num)]
    exact EqDv 33 (by norm_num)
  · rw [gv_eq_T 417 (by norm_num)]
    exact DnDv 33 (by norm_num)

theorem bnd_418 : Gv 418 = 14231234289 ∧ LOG1E13LB ≤ gv 418 := by
  constructor
  · rw [Gv_eq_T 418 (by norm_num)]
    exact EqDv 34 (by norm_num)
  · rw [gv_eq_T 418 (by norm_num)]
    exact DnDv 34 (by norm_num)

theorem bnd_419 : Gv 419 = 14235448083 ∧ LOG1E13LB ≤ gv 419 := by
  constructor
  · rw [Gv_eq_T 419 (by norm_num)]
    exact EqDv 35 (by norm_num)
  · rw [gv_eq_T 419 (by norm_num)]
    exact DnDv 35 (by norm_num)

theorem bnd_420 : Gv 420 = 14239596541 ∧ LOG1E13LB ≤ gv 420 := by
  constructor
  · rw [Gv_eq_T 420 (by norm_num)]
    exact EqDv 36 (by norm_num)
  · rw [gv_eq_T 420 (by norm_num)]
    exact DnDv 36 (by norm_num)

theorem bnd_421 : Gv 421 = 14243678423 ∧ LOG1E13LB ≤ gv 421 := by
  constructor
  · rw [Gv_eq_T 421 (by norm_num)]
    exact EqDv 37 (by norm_num)
  · rw [gv_eq_T 421 (by norm_num)]
    exact DnDv 37 (by norm_num)

theorem bnd_422 : Gv 422 = 14247693909 ∧ LOG1E13LB ≤ gv 422 := by
  constructor
  · rw [Gv_eq_T 422 (by norm_num)]
    exact EqDv 38 (by norm_num)
  · rw [gv_eq_T 422 (by norm_num)]
    exact DnDv 38 (by norm_num)

theorem bnd_423 : Gv 423 = 14251649445 ∧ LOG1E13LB ≤ gv 423 := by
  constructor
  · rw [Gv_eq_T 423 (by norm_num)]
    exact EqDv 39 (by norm_num)
  · rw [gv_eq_T 423 (by norm_num)]
    exact DnDv 39 (by norm_num)

theorem bnd_424 : Gv 424 = 14255545319 ∧ LOG1E13LB ≤ gv 424 := by
  constructor
  · rw [Gv_eq_T 424 (by norm_num)]
    exact EqDv 40 (by norm_num)
  · rw [gv_eq_T 424 (by norm_num)]
    exact DnDv 40 (by norm_num)

theorem bnd_425 : Gv 425 = 14259372063 ∧ LOG1E13LB ≤ gv 425 := by
  constructor
  · rw [Gv_eq_T 425 (by norm_num)]
    exact EqDv 41 (by norm_num)
  · rw [gv_eq_T 425 (by norm_num)]
    exact DnDv 41 (by norm_num)

theorem bnd_426 : Gv 426 = 14263141667 ∧ LOG1E13LB ≤ gv 426 := by
  constructor
  · rw [Gv_eq_T 426 (by norm_num)]
    exact EqDv 42 (by norm_num)
  · rw [gv_eq_T 426 (by norm_num)]
    exact DnDv 42 (by norm_num)

theorem bnd_427 : Gv 427 = 14266853095 ∧ LOG1E13LB ≤ gv 427 := by
  constructor
  · rw [Gv_eq_T 427 (by norm_num)]
    exact EqDv 43 (by norm_num)
  · rw [gv_eq_T 427 (by norm_num)]
    exact DnDv 43 (by norm_num)

theorem bnd_428 : Gv 428 = 14270501355 ∧ LOG1E13LB ≤ gv 428 := by
  constructor
  · rw [Gv_eq_T 428 (by norm_num)]
    exact EqDv 44 (by norm_num)
  · rw [gv_eq_T 428 (by norm_num)]
    exact DnDv 44 (by norm_num)

theorem bnd_429 : Gv 429 = 14274090751 ∧ LOG1E13LB ≤ gv 429 := by
  constructor
  · rw [Gv_eq_T 429 (by norm_num)]
    exact EqDv 45 (by norm_num)
  · rw [gv_eq_T 429 (by norm_num)]
    exact DnDv 45 (by norm_num)

theorem bnd_430 : Gv 430 = 14277616793 ∧ LOG1E13LB ≤ gv 430 := by
  constructor
  · rw [Gv_eq_T 430 (by norm_num)]
    exact EqDv 46 (by norm_num)
  · rw [gv_eq_T 430 (by norm_num)]
    exact DnDv 46 (by norm_num)

theorem bnd_431 : Gv 431 = 14281089863 ∧ LOG1E13LB ≤ gv 431 := by
  constructor
  · rw [Gv_eq_T 431 (by norm_num)]
    exact EqDv 47 (by norm_num)
  · rw [gv_eq_T 431 (by norm_num)]
    exact DnDv 47 (by norm_num)

theorem bnd_432 : Gv 432 = 14284507005 ∧ LOG1E13LB ≤ gv 432 := by
  constructor
  · rw [Gv_eq_T 432 (by norm_num)]
    exact EqDv 48 (by norm_num)
  · rw [gv_eq_T 432 (by norm_num)]
    exact DnDv 48 (by norm_num)

theorem bnd_433 : Gv 433 = 14287862239 ∧ LOG1E13LB ≤ gv 433 := by
  constructor
  · rw [Gv_eq_T 433 (by norm_num)]
    exact EqDv 49 (by norm_num)
  · rw [gv_eq_T 433 (by norm_num)]
    exact DnDv 49 (by norm_num)

theorem bnd_434 : Gv 434 = 14291164177 ∧ LOG1E13LB ≤ gv 434 := by
  constructor
  · rw [Gv_eq_T 434 (by norm_num)]
    exact EqDv 50 (by norm_num)
  · rw [gv_eq_T 434 (by norm_num)]
    exact DnDv 50 (by norm_num)

theorem bnd_435 : Gv 435 = 14294413945 ∧ LOG1E13LB ≤ gv 435 := by
  constructor
  · rw [Gv_eq_T 435 (by norm_num)]
    exact EqDv 51 (by norm_num)
  · rw [gv_eq_T 435 (by norm_num)]
    exact DnDv 51 (by norm_num)

theorem bnd_436 : Gv 436 = 14297600909 ∧ LOG1E13LB ≤ gv 436 := by
  constructor
  · rw [Gv_eq_T 436 (by norm_num)]
    exact EqDv 52 (by norm_num)
  · rw [gv_eq_T 436 (by norm_num)]
    exact DnDv 52 (by norm_num)

theorem bnd_437 : Gv 437 = 14300741663 ∧ LOG1E13LB ≤ gv 437 := by
  constructor
  · rw [Gv_eq_T 437 (by norm_num)]
    exact EqDv 53 (by norm_num)
  · rw [gv_eq_T 437 (by norm_num)]
    exact DnDv 53 (by norm_num)

theorem bnd_438 : Gv 438 = 14303820677 ∧ LOG1E13LB ≤ gv 438 := by
  constructor
  · rw [Gv_eq_T 438 (by norm_num)]
    exact EqDv 54 (by norm_num)
  · rw [gv_eq_T 438 (by norm_num)]
    exact DnDv 54 (by norm_num)

theorem bnd_439 : Gv 439 = 14306850493 ∧ LOG1E13LB ≤ gv 439 := by
  constructor
  · rw [Gv_eq_T 439 (by norm_num)]
    exact EqDv 55 (by norm_num)
  · rw [gv_eq_T 439 (by norm_num)]
    exact DnDv 55 (by norm_num)

theorem bnd_440 : Gv 440 = 14309826197 ∧ LOG1E13LB ≤ gv 440 := by
  constructor
  · rw [Gv_eq_T 440 (by norm_num)]
    exact EqDv 56 (by norm_num)
  · rw [gv_eq_T 440 (by norm_num)]
    exact DnDv 56 (by norm_num)

theorem bnd_441 : Gv 441 = 14312750649 ∧ LOG1E13LB ≤ gv 441 := by
  constructor
  · rw [Gv_eq_T 441 (by norm_num)]
    exact EqDv 57 (by norm_num)
  · rw [gv_eq_T 441 (by norm_num)]
    exact DnDv 57 (by norm_num)

theorem bnd_442 : Gv 442 = 14315621793 ∧ LOG1E13LB ≤ gv 442 := by
  constructor
  · rw [Gv_eq_T 442 (by norm_num)]
    exact EqDv 58 (by norm_num)
  · rw [gv_eq_T 442 (by norm_num)]
    exact DnDv 58 (by norm_num)

theorem bnd_443 : Gv 443 = 14318444381 ∧ LOG1E13LB ≤ gv 443 := by
  constructor
  · rw [Gv_eq_T 443 (by norm_num)]
    exact EqDv 59 (by norm_num)
  · rw [gv_eq_T 443 (by norm_num)]
    exact DnDv 59 (by norm_num)

theorem bnd_444 : Gv 444 = 14321213979 ∧ LOG1E13LB ≤ gv 444 := by
  constructor
  · rw [Gv_eq_T 444 (by norm_num)]
    exact EqDv 60 (by norm_num)
  · rw [gv_eq_T 444 (by norm_num)]
    exact DnDv 60 (by norm_num)

theorem bnd_445 : Gv 445 = 14323934787 ∧ LOG1E13LB ≤ gv 445 := by
  constructor
  · rw [Gv_eq_T 445 (by norm_num)]
    exact EqDv 61 (by norm_num)
  · rw [gv_eq_T 445 (by norm_num)]
    exact DnDv 61 (by norm_num)

theorem bnd_446 : Gv 446 = 14326597651 ∧ LOG1E13LB ≤ gv 446 := by
  constructor
  · rw [Gv_eq_T 446 (by norm_num)]
    exact EqDv 62 (by norm_num)
  · rw [gv_eq_T 446 (by norm_num)]
    exact DnDv 62 (by norm_num)

theorem bnd_447 : Gv 447 = 14329224921 ∧ LOG1E13LB ≤ gv 447 := by
  constructor
  · rw [Gv_eq_T 447 (by norm_num)]
    exact EqDv 63 (by norm_num)
  · rw [gv_eq_T 447 (by norm_num)]
    exact DnDv 63 (by norm_num)

theorem bnd_448 : Gv 448 = 14331796009 ∧ LOG1E13LB ≤ gv 448 := by
  constructor
  · rw [Gv_eq_T 448 (by norm_num)]
    exact EqDv 64 (by norm_num)
  · rw [gv_eq_T 448 (by norm_num)]
    exact DnDv 64 (by norm_num)

theorem bnd_449 : Gv 449 = 14334313841 ∧ LOG1E13LB ≤ gv 449 := by
  constructor
  · rw [Gv_eq_T 449 (by norm_num)]
    exact EqDv 65 (by norm_num)
  · rw [gv_eq_T 449 (by norm_num)]
    exact DnDv 65 (by norm_num)

theorem bnd_450 : Gv 450 = 14336789467 ∧ LOG1E13LB ≤ gv 450 := by
  constructor
  · rw [Gv_eq_T 450 (by norm_num)]
    exact EqDv 66 (by norm_num)
  · rw [gv_eq_T 450 (by norm_num)]
    exact DnDv 66 (by norm_num)

theorem bnd_451 : Gv 451 = 14339217181 ∧ LOG1E13LB ≤ gv 451 := by
  constructor
  · rw [Gv_eq_T 451 (by norm_num)]
    exact EqDv 67 (by norm_num)
  · rw [gv_eq_T 451 (by norm_num)]
    exact DnDv 67 (by norm_num)

theorem bnd_452 : Gv 452 = 14341596441 ∧ LOG1E13LB ≤ gv 452 := by
  constructor
  · rw [Gv_eq_T 452 (by norm_num)]
    exact EqDv 68 (by norm_num)
  · rw [gv_eq_T 452 (by norm_num)]
    exact DnDv 68 (by norm_num)

theorem bnd_453 : Gv 453 = 14343926123 ∧ LOG1E13LB ≤ gv 453 := by
  constructor
  · rw [Gv_eq_T 453 (by norm_num)]
    exact EqDv 69 (by norm_num)
  · rw [gv_eq_T 453 (by norm_num)]
    exact DnDv 69 (by norm_num)

theorem bnd_454 : Gv 454 = 14346214025 ∧ LOG1E13LB ≤ gv 454 := by
  constructor
  · rw [Gv_eq_T 454 (by norm_num)]
    exact EqDv 70 (by norm_num)
  · rw [gv_eq_T 454 (by norm_num)]
    exact DnDv 70 (by norm_num)

theorem bnd_455 : Gv 455 = 14348452119 ∧ LOG1E13LB ≤ gv 455 := by
  constructor
  · rw [Gv_eq_T 455 (by norm_num)]
    exact EqDv 71 (by norm_num)
  · rw [gv_eq_T 455 (by norm_num)]
    exact DnDv 71 (by norm_num)

theorem bnd_456 : Gv 456 = 14350645901 ∧ LOG1E13LB ≤ gv 456 := by
  constructor
  · rw [Gv_eq_T 456 (by norm_num)]
    exact EqDv 72 (by norm_num)
  · rw [gv_eq_T 456 (by norm_num)]
    exact DnDv 72 (by norm_num)

theorem bnd_457 : Gv 457 = 14352792427 ∧ LOG1E13LB ≤ gv 457 := by
  constructor
  · rw [Gv_eq_T 457 (by norm_num)]
    exact EqDv 73 (by norm_num)
  · rw [gv_eq_T 457 (by norm_num)]
    exact DnDv 73 (by norm_num)

theorem bnd_458 : Gv 458 = 14354891855 ∧ LOG1E13LB ≤ gv 458 := by
  constructor
  · rw [Gv_eq_T 458 (by norm_num)]
    exact EqDv 74 (by norm_num)
  · rw [gv_eq_T 458 (by norm_num)]
    exact DnDv 74 (by norm_num)

theorem bnd_459 : Gv 459 = 14356952913 ∧ LOG1E13LB ≤ gv 459 := by
  constructor
  · rw [Gv_eq_T 459 (by norm_num)]
    exact EqDv 75 (by norm_num)
  · rw [gv_eq_T 459 (by norm_num)]
    exact DnDv 75 (by norm_num)

theorem bnd_460 : Gv 460 = 14358961395 ∧ LOG1E13LB ≤ gv 460 := by
  constructor
  · rw [Gv_eq_T 460 (by norm_num)]
    exact EqDv 76 (by norm_num)
  · rw [gv_eq_T 460 (by norm_num)]
    exact DnDv 76 (by norm_num)

theorem bnd_461 : Gv 461 = 14360929003 ∧ LOG1E13LB ≤ gv 461 := by
  constructor
  · rw [Gv_eq_T 461 (by norm_num)]
    exact EqDv 77 (by norm_num)
  · rw [gv_eq_T 461 (by norm_num)]
    exact DnDv 77 (by norm_num)

theorem bnd_462 : Gv 462 = 14362857571 ∧ LOG1E13LB ≤ gv 462 := by
  constructor
  · rw [Gv_eq_T 462 (by norm_num)]
    exact EqDv 78 (by norm_num)
  · rw [gv_eq_T 462 (by norm_num)]
    exact DnDv 78 (by norm_num)

theorem bnd_463 : Gv 463 = 14364739743 ∧ LOG1E13LB ≤ gv 463 := by
  constructor
  · rw [Gv_eq_T 463 (by norm_num)]
    exact EqDv 79 (by norm_num)
  · rw [gv_eq_T 463 (by norm_num)]
    exact DnDv 79 (by norm_num)

theorem bnd_464 : Gv 464 = 14366574205 ∧ LOG1E13LB ≤ gv 464 := by
  constructor
  · rw [Gv_eq_T 464 (by norm_num)]
    exact EqDv 80 (by norm_num)
  · rw [gv_eq_T 464 (by norm_num)]
    exact DnDv 80 (by norm_num)

theorem bnd_465 : Gv 465 = 14368371897 ∧ LOG1E13LB ≤ gv 465 := by
  constructor
  · rw [Gv_eq_T 465 (by norm_num)]
    exact EqDv 81 (by norm_num)
  · rw [gv_eq_T 465 (by norm_num)]
    exact DnDv 81 (by norm_num)

theorem bnd_466 : Gv 466 = 14370124763 ∧ LOG1E13LB ≤ gv 466 := by
  constructor
  · rw [Gv_eq_T 466 (by norm_num)]
    exact EqDv 82 (by norm_num)
  · rw [gv_eq_T 466 (by norm_num)]
    exact DnDv 82 (by norm_num)

theorem bnd_467 : Gv 467 = 14371831739 ∧ LOG1E13LB ≤ gv 467 := by
  constructor
  · rw [Gv_eq_T 467 (by norm_num)]
    exact EqDv 83 (by norm_num)
  · rw [gv_eq_T 467 (by norm_num)]
    exact DnDv 83 (by norm_num)

theorem bnd_468 : Gv 468 = 14373501661 ∧ LOG1E13LB ≤ gv 468 := by
  constructor
  · rw [Gv_eq_T 468 (by norm_num)]
    exact EqDv 84 (by norm_num)
  · rw [gv_eq_T 468 (by norm_num)]
    exact DnDv 84 (by norm_num)

theorem bnd_469 : Gv 469 = 14375129849 ∧ LOG1E13LB ≤ gv 469 := by
  constructor
  · rw [Gv_eq_T 469 (by norm_num)]
    exact EqDv 85 (by norm_num)
  · rw [gv_eq_T 469 (by norm_num)]
    exact DnDv 85 (by norm_num)

theorem bnd_470 : Gv 470 = 14376711979 ∧ LOG1E13LB ≤ gv 470 := by
  constructor
  · rw [Gv_eq_T 470 (by norm_num)]
    exact EqDv 86 (by norm_num)
  · rw [gv_eq_T 470 (by norm_num)]
    exact DnDv 86 (by norm_num)

theorem bnd_471 : Gv 471 = 14378253961 ∧ LOG1E13LB ≤ gv 471 := by
  constructor
  · rw [Gv_eq_T 471 (by norm_num)]
    exact EqDv 87 (by norm_num)
  · rw [gv_eq_T 471 (by norm_num)]
    exact DnDv 87 (by norm_num)

theorem bnd_472 : Gv 472 = 14379753417 ∧ LOG1E13LB ≤ gv 472 := by
  constructor
  · rw [Gv_eq_T 472 (by norm_num)]
    exact EqDv 88 (by norm_num)
  · rw [gv_eq_T 472 (by norm_num)]
    exact DnDv 88 (by norm_num)

theorem bnd_473 : Gv 473 = 14381211729 ∧ LOG1E13LB ≤ gv 473 := by
  constructor
  · rw [Gv_eq_T 473 (by norm_num)]
    exact EqDv 89 (by norm_num)
  · rw [gv_eq_T 473 (by norm_num)]
    exact DnDv 89 (by norm_num)

theorem bnd_474 : Gv 474 = 14382631791 ∧ LOG1E13LB ≤ gv 474 := by
  constructor
  · rw [Gv_eq_T 474 (by norm_num)]
    exact EqDv 90 (by norm_num)
  · rw [gv_eq_T 474 (by norm_num)]
    exact DnDv 90 (by norm_num)

theorem bnd_475 : Gv 475 = 14384014941 ∧ LOG1E13LB ≤ gv 475 := by
  constructor
  · rw [Gv_eq_T 475 (by norm_num)]
    exact EqDv 91 (by norm_num)
  · rw [gv_eq_T 475 (by norm_num)]
    exact DnDv 91 (by norm_num)

theorem bnd_476 : Gv 476 = 14385351705 ∧ LOG1E13LB ≤ gv 476 := by
  constructor
  · rw [Gv_eq_T 476 (by norm_num)]
    exact EqDv 92 (by norm_num)
  · rw [gv_eq_T 476 (by norm_num)]
    exact DnDv 92 (by norm_num)

theorem bnd_477 : Gv 477 = 14386650827 ∧ LOG1E13LB ≤ gv 477 := by
  constructor
  · rw [Gv_eq_T 477 (by norm_num)]
    exact EqDv 93 (by norm_num)
  · rw [gv_eq_T 477 (by norm_num)]
    exact DnDv 93 (by norm_num)

theorem bnd_478 : Gv 478 = 14387909121 ∧ LOG1E13LB ≤ gv 478 := by
  constructor
  · rw [Gv_eq_T 478 (by norm_num)]
    exact EqDv 94 (by norm_num)
  · rw [gv_eq_T 478 (by norm_num)]
    exact DnDv 94 (by norm_num)

theorem bnd_479 : Gv 479 = 14389130257 ∧ LOG1E13LB ≤ gv 479 := by
  constructor
  · rw [Gv_eq_T 479 (by norm_num)]
    exact EqDv 95 (by norm_num)
  · rw [gv_eq_T 479 (by norm_num)]
    exact DnDv 95 (by norm_num)

theorem bnd_480 : Gv 480 = 14390311469 ∧ LOG1E13LB ≤ gv 480 := by
  constructor
  · rw [Gv_eq_T 480 (by norm_num)]
    exact EqDv 96 (by norm_num)
  · rw [gv_eq_T 480 (by norm_num)]
    exact DnDv 96 (by norm_num)

theorem bnd_481 : Gv 481 = 14391454769 ∧ LOG1E13LB ≤ gv 481 := by
  constructor
  · rw [Gv_eq_T 481 (by norm_num)]
    exact EqDv 97 (by norm_num)
  · rw [gv_eq_T 481 (by norm_num)]
    exact DnDv 97 (by norm_num)

theorem bnd_482 : Gv 482 = 14392551813 ∧ LOG1E13LB ≤ gv 482 := by
  constructor
  · rw [Gv_eq_T 482 (by norm_num)]
    exact EqDv 98 (by norm_num)
  · rw [gv_eq_T 482 (by norm_num)]
    exact DnDv 98 (by norm_num)

theorem bnd_483 : Gv 483 = 14393615419 ∧ LOG1E13LB ≤ gv 483 := by
  constructor
  · rw [Gv_eq_T 483 (by norm_num)]
    exact EqDv 99 (by norm_num)
  · rw [gv_eq_T 483 (by norm_num)]
    exact DnDv 99 (by norm_num)

theorem bnd_484 : Gv 484 = 14394639035 ∧ LOG1E13LB ≤ gv 484 := by
  constructor
  · rw [Gv_eq_T 484 (by norm_num)]
    exact EqDv 100 (by norm_num)
  · rw [gv_eq_T 484 (by norm_num)]
    exact DnDv 100 (by norm_num)

theorem bnd_485 : Gv 485 = 14395626869 ∧ LOG1E13LB ≤ gv 485 := by
  constructor
  · rw [Gv_eq_T 485 (by norm_num)]
    exact EqDv 101 (by norm_num)
  · rw [gv_eq_T 485 (by norm_num)]
    exact DnDv 101 (by norm_num)

theorem bnd_486 : Gv 486 = 14396572467 ∧ LOG1E13LB ≤ gv 486 := by
  constructor
  · rw [Gv_eq_T 486 (by norm_num)]
    exact EqDv 102 (by norm_num)
  · rw [gv_eq_T 486 (by norm_num)]
    exact DnDv 102 (by norm_num)

theorem bnd_487 : Gv 487 = 14397481721 ∧ LOG1E13LB ≤ gv 487 := by
  constructor
  · rw [Gv_eq_T 487 (by norm_num)]
    exact EqDv 103 (by norm_num)
  · rw [gv_eq_T 487 (by norm_num)]
    exact DnDv 103 (by norm_num)

theorem bnd_488 : Gv 488 = 14398354285 ∧ LOG1E13LB ≤ gv 488 := by
  constructor
  · rw [Gv_eq_T 488 (by norm_num)]
    exact EqDv 104 (by norm_num)
  · rw [gv_eq_T 488 (by norm_num)]
    exact DnDv 104 (by norm_num)

theorem bnd_489 : Gv 489 = 14399186919 ∧ LOG1E13LB ≤ gv 489 := by
  constructor
  · rw [Gv_eq_T 489 (by norm_num)]
    exact EqDv 105 (by norm_num)
  · rw [gv_eq_T 489 (by norm_num)]
    exact DnDv 105 (by norm_num)

theorem bnd_490 : Gv 490 = 14399979953 ∧ LOG1E13LB ≤ gv 490 := by
  constructor
  · rw [Gv_eq_T 490 (by norm_num)]
    exact EqDv 106 (by norm_num)
  · rw [gv_eq_T 490 (by norm_num)]
    exact DnDv 106 (by norm_num)

theorem bnd_491 : Gv 491 = 14400738413 ∧ LOG1E13LB ≤ gv 491 := by
  constructor
  · rw [Gv_eq_T 491 (by norm_num)]
    exact EqDv 107 (by norm_num)
  · rw [gv_eq_T 491 (by norm_num)]
    exact DnDv 107 (by norm_num)

theorem bnd_492 : Gv 492 = 14401460371 ∧ LOG1E13LB ≤ gv 492 := by
  constructor
  · rw [Gv_eq_T 492 (by norm_num)]
    exact EqDv 108 (by norm_num)
  · rw [gv_eq_T 492 (by norm_num)]
    exact DnDv 108 (by norm_num)

theorem bnd_493 : Gv 493 = 14402136757 ∧ LOG1E13LB ≤ gv 493 := by
  constructor
  · rw [Gv_eq_T 493 (by norm_num)]
    exact EqDv 109 (by norm_num)
  · rw [gv_eq_T 493 (by norm_num)]
    exact DnDv 109 (by norm_num)

theorem bnd_494 : Gv 494 = 14402782445 ∧ LOG1E13LB ≤ gv 494 := by
  constructor
  · rw [Gv_eq_T 494 (by norm_num)]
    exact EqDv 110 (by norm_num)
  · rw [gv_eq_T 494 (by norm_num)]
    exact DnDv 110 (by norm_num)

theorem bnd_495 : Gv 495 = 14403394327 ∧ LOG1E13LB ≤ gv 495 := by
  constructor
  · rw [Gv_eq_T 495 (by norm_num)]
    exact EqDv 111 (by norm_num)
  · rw [gv_eq_T 495 (by norm_num)]
    exact DnDv 111 (by norm_num)

theorem bnd_496 : Gv 496 = 14403959233 ∧ LOG1E13LB ≤ gv 496 := by
  constructor
  · rw [Gv_eq_T 496 (by norm_num)]
    exact EqDv 112 (by norm_num)
  · rw [gv_eq_T 496 (by norm_num)]
    exact DnDv 112 (by norm_num)

theorem bnd_497 : Gv 497 = 14404493911 ∧ LOG1E13LB ≤ gv 497 := by
  constructor
  · rw [Gv_eq_T 497 (by norm_num)]
    exact EqDv 113 (by norm_num)
  · rw [gv_eq_T 497 (by norm_num)]
    exact DnDv 113 (by norm_num)

theorem bnd_498 : Gv 498 = 14404992987 ∧ LOG1E13LB ≤ gv 498 := by
  constructor
  · rw [Gv_eq_T 498 (by norm_num)]
    exact EqDv 114 (by norm_num)
  · rw [gv_eq_T 498 (by norm_num)]
    exact DnDv 114 (by norm_num)

theorem bnd_499 : Gv 499 = 14405448321 ∧ LOG1E13LB ≤ gv 499 := by
  constructor
  · rw [Gv_eq_T 499 (by norm_num)]
    exact EqDv 115 (by norm_num)
  · rw [gv_eq_T 499 (by norm_num)]
    exact DnDv 115 (by norm_num)

theorem bnd_500 : Gv 500 = 14405869815 ∧ LOG1E13LB ≤ gv 500 := by
  constructor
  · rw [Gv_eq_T 500 (by norm_num)]
    exact EqDv 116 (by norm_num)
  · rw [gv_eq_T 500 (by norm_num)]
    exact DnDv 116 (by norm_num)

theorem bnd_501 : Gv 501 = 14406254619 ∧ LOG1E13LB ≤ gv 501 := by
  constructor
  · rw [Gv_eq_T 501 (by norm_num)]
    exact EqDv 117 (by norm_num)
  · rw [gv_eq_T 501 (by norm_num)]
    exact DnDv 117 (by norm_num)

theorem bnd_502 : Gv 502 = 14406602339 ∧ LOG1E13LB ≤ gv 502 := by
  constructor
  · rw [Gv_eq_T 502 (by norm_num)]
    exact EqDv 118 (by norm_num)
  · rw [gv_eq_T 502 (by norm_num)]
    exact DnDv 118 (by norm_num)

theorem bnd_503 : Gv 503 = 14406911585 ∧ LOG1E13LB ≤ gv 503 := by
  constructor
  · rw [Gv_eq_T 503 (by norm_num)]
    exact EqDv 119 (by norm_num)
  · rw [gv_eq_T 503 (by norm_num)]
    exact DnDv 119 (by norm_num)

theorem bnd_504 : Gv 504 = 14407190947 ∧ LOG1E13LB ≤ gv 504 := by
  constructor
  · rw [Gv_eq_T 504 (by norm_num)]
    exact EqDv 120 (by norm_num)
  · rw [gv_eq_T 504 (by norm_num)]
    exact DnDv 120 (by norm_num)

theorem bnd_505 : Gv 505 = 14407423991 ∧ LOG1E13LB ≤ gv 505 := by
  constructor
  · rw [Gv_eq_T 505 (by norm_num)]
    exact EqDv 121 (by norm_num)
  · rw [gv_eq_T 505 (by norm_num)]
    exact DnDv 121 (by norm_num)

theorem bnd_506 : Gv 506 = 14407624645 ∧ LOG1E13LB ≤ gv 506 := by
  constructor
  · rw [Gv_eq_T 506 (by norm_num)]
    exact EqDv 122 (by norm_num)
  · rw [gv_eq_T 506 (by norm_num)]
    exact DnDv 122 (by norm_num)

theorem bnd_507 : Gv 507 = 14407791217 ∧ LOG1E13LB ≤ gv 507 := by
  constructor
  · rw [Gv_eq_T 507 (by norm_num)]
    exact EqDv 123 (by norm_num)
  · rw [gv_eq_T 507 (by norm_num)]
    exact DnDv 123 (by norm_num)

theorem bnd_508 : Gv 508 = 14407919439 ∧ LOG1E13LB ≤ gv 508 := by
  constructor
  · rw [Gv_eq_T 508 (by norm_num)]
    exact EqDv 124 (by norm_num)
  · rw [gv_eq_T 508 (by norm_num)]
    exact DnDv 124 (by norm_num)

theorem bnd_509 : Gv 509 = 14408010127 ∧ LOG1E13LB ≤ gv 509 := by
  constructor
  · rw [Gv_eq_T 509 (by norm_num)]
    exact EqDv 125 (by norm_num)
  · rw [gv_eq_T 509 (by norm_num)]
    exact DnDv 125 (by norm_num)

theorem bnd_510 : Gv 510 = 14408068463 ∧ LOG1E13LB ≤ gv 510 := by
  constructor
  · rw [Gv_eq_T 510 (by norm_num)]
    exact EqDv 126 (by norm_num)
  · rw [gv_eq_T 510 (by norm_num)]
    exact DnDv 126 (by norm_num)

theorem bnd_511 : Gv 511 = 14408068463 ∧ LOG1E13LB ≤ gv 511 := by
  constructor
  · rw [Gv_eq_T 511 (by norm_num)]
    exact EqDv 127 (by norm_num)
  · rw [gv_eq_T 511 (by norm_num)]
    exact DnDv 127 (by norm_num)

theorem bnd_512 : Gv 512 = 14408042617 ∧ LOG1E13LB ≤ gv 512 := by
  constructor
  · rw [Gv_eq_T 512 (by norm_num)]
    exact EqEv 0 (by norm_num)
  · rw [gv_eq_T 512 (by norm_num)]
    exact DnEv 0 (by norm_num)

theorem bnd_513 : Gv 513 = 14408042617 ∧ LOG1E13LB ≤ gv 513 := by
  constructor
  · rw [Gv_eq_T 513 (by norm_num)]
    exact EqEv 1 (by norm_num)
  · rw [gv_eq_T 513 (by norm_num)]
    exact DnEv 1 (by norm_num)

theorem bnd_514 : Gv 514 = 14407987703 ∧ LOG1E13LB ≤ gv 514 := by
  constructor
  · rw [Gv_eq_T 514 (by norm_num)]
    exact EqEv 2 (by norm_num)
  · rw [gv_eq_T 514 (by norm_num)]
    exact DnEv 2 (by norm_num)

theorem bnd_515 : Gv 515 = 14407897059 ∧ LOG1E13LB ≤ gv 515 := by
  constructor
  · rw [Gv_eq_T 515 (by norm_num)]
    exact EqEv 3 (by norm_num)
  · rw [gv_eq_T 515 (by norm_num)]
    exact DnEv 3 (by norm_num)

theorem bnd_516 : Gv 516 = 14407771485 ∧ LOG1E13LB ≤ gv 516 := by
  constructor
  · rw [Gv_eq_T 516 (by norm_num)]
    exact EqEv 4 (by norm_num)
  · rw [gv_eq_T 516 (by norm_num)]
    exact DnEv 4 (by norm_num)

theorem bnd_517 : Gv 517 = 14407603999 ∧ LOG1E13LB ≤ gv 517 := by
  constructor
  · rw [Gv_eq_T 517 (by norm_num)]
    exact EqEv 5 (by norm_num)
  · rw [gv_eq_T 517 (by norm_num)]
    exact DnEv 5 (by norm_num)

theorem bnd_518 : Gv 518 = 14407403341 ∧ LOG1E13LB ≤ gv 518 := by
  constructor
  · rw [Gv_eq_T 518 (by norm_num)]
    exact EqEv 6 (by norm_num)
  · rw [gv_eq_T 518 (by norm_num)]
    exact DnEv 6 (by norm_num)

theorem bnd_519 : Gv 519 = 14407166067 ∧ LOG1E13LB ≤ gv 519 := by
  constructor
  · rw [Gv_eq_T 519 (by norm_num)]
    exact EqEv 7 (by norm_num)
  · rw [gv_eq_T 519 (by norm_num)]
    exact DnEv 7 (by norm_num)

theorem bnd_520 : Gv 520 = 14406890985 ∧ LOG1E13LB ≤ gv 520 := by
  constructor
  · rw [Gv_eq_T 520 (by norm_num)]
    exact EqEv 8 (by norm_num)
  · rw [gv_eq_T 520 (by norm_num)]
    exact DnEv 8 (by norm_num)

theorem bnd_521 : Gv 521 = 14406582415 ∧ LOG1E13LB ≤ gv 521 := by
  constructor
  · rw [Gv_eq_T 521 (by norm_num)]
    exact EqEv 9 (by norm_num)
  · rw [gv_eq_T 521 (by norm_num)]
    exact DnEv 9 (by norm_num)

theorem bnd_522 : Gv 522 = 14406232187 ∧ LOG1E13LB ≤ gv 522 := by
  constructor
  · rw [Gv_eq_T 522 (by norm_num)]
    exact EqEv 10 (by norm_num)
  · rw [gv_eq_T 522 (by norm_num)]
    exact DnEv 10 (by norm_num)

theorem bnd_523 : Gv 523 = 14405850125 ∧ LOG1E13LB ≤ gv 523 := by
  constructor
  · rw [Gv_eq_T 523 (by norm_num)]
    exact EqEv 11 (by norm_num)
  · rw [gv_eq_T 523 (by norm_num)]
    exact DnEv 11 (by norm_num)

theorem bnd_524 : Gv 524 = 14405425943 ∧ LOG1E13LB ≤ gv 524 := by
  constructor
  · rw [Gv_eq_T 524 (by norm_num)]
    exact EqEv 12 (by norm_num)
  · rw [gv_eq_T 524 (by norm_num)]
    exact DnEv 12 (by norm_num)

theorem bnd_525 : Gv 525 = 14404967145 ∧ LOG1E13LB ≤ gv 525 := by
  constructor
  · rw [Gv_eq_T 525 (by norm_num)]
    exact EqEv 13 (by norm_num)
  · rw [gv_eq_T 525 (by norm_num)]
    exact DnEv 13 (by norm_num)

theorem bnd_526 : Gv 526 = 14404471533 ∧ LOG1E13LB ≤ gv 526 := by
  constructor
  · rw [Gv_eq_T 526 (by norm_num)]
    exact EqEv 14 (by norm_num)
  · rw [gv_eq_T 526 (by norm_num)]
    exact DnEv 14 (by norm_num)

theorem bnd_527 : Gv 527 = 14403938535 ∧ LOG1E13LB ≤ gv 527 := by
  constructor
  · rw [Gv_eq_T 527 (by norm_num)]
    exact EqEv 15 (by norm_num)
  · rw [gv_eq_T 527 (by norm_num)]
    exact DnEv 15 (by norm_num)

theorem bnd_528 : Gv 528 = 14403369397 ∧ LOG1E13LB ≤ gv 528 := by
  constructor
  · rw [Gv_eq_T 528 (by norm_num)]
    exact EqEv 16 (by norm_num)
  · rw [gv_eq_T 528 (by norm_num)]
    exact DnEv 16 (by norm_num)

theorem bnd_529 : Gv 529 = 14402764397 ∧ LOG1E13LB ≤ gv 529 := by
  constructor
  · rw [Gv_eq_T 529 (by norm_num)]
    exact EqEv 17 (by norm_num)
  · rw [gv_eq_T 529 (by norm_num)]
    exact DnEv 17 (by norm_num)

theorem bnd_530 : Gv 530 = 14402120343 ∧ LOG1E13LB ≤ gv 530 := by
  constructor
  · rw [Gv_eq_T 530 (by norm_num)]
    exact EqEv 18 (by norm_num)
  · rw [gv_eq_T 530 (by norm_num)]
    exact DnEv 18 (by norm_num)

theorem bnd_531 : Gv 531 = 14401435391 ∧ LOG1E13LB ≤ gv 531 := by
  constructor
  · rw [Gv_eq_T 531 (by norm_num)]
    exact EqEv 19 (by norm_num)
  · rw [gv_eq_T 531 (by norm_num)]
    exact DnEv 19 (by norm_num)

theorem bnd_532 : Gv 532 = 14400718729 ∧ LOG1E13LB ≤ gv 532 := by
  constructor
  · rw [Gv_eq_T 532 (by norm_num)]
    exact EqEv 20 (by norm_num)
  · rw [gv_eq_T 532 (by norm_num)]
    exact DnEv 20 (by norm_num)

theorem bnd_533 : Gv 533 = 14399959253 ∧ LOG1E13LB ≤ gv 533 := by
  constructor
  · rw [Gv_eq_T 533 (by norm_num)]
    exact EqEv 21 (by norm_num)
  · rw [gv_eq_T 533 (by norm_num)]
    exact DnEv 21 (by norm_num)

theorem bnd_534 : Gv 534 = 14399164491 ∧ LOG1E13LB ≤ gv 534 := by
  constructor
  · rw [Gv_eq_T 534 (by norm_num)]
    exact EqEv 22 (by norm_num)
  · rw [gv_eq_T 534 (by norm_num)]
    exact DnEv 22 (by norm_num)

theorem bnd_535 : Gv 535 = 14398331807 ∧ LOG1E13LB ≤ gv 535 := by
  constructor
  · rw [Gv_eq_T 535 (by norm_num)]
    exact EqEv 23 (by norm_num)
  · rw [gv_eq_T 535 (by norm_num)]
    exact DnEv 23 (by norm_num)

theorem bnd_536 : Gv 536 = 14397463671 ∧ LOG1E13LB ≤ gv 536 := by
  constructor
  · rw [Gv_eq_T 536 (by norm_num)]
    exact EqEv 24 (by norm_num)
  · rw [gv_eq_T 536 (by norm_num)]
    exact DnEv 24 (by norm_num)

theorem bnd_537 : Gv 537 = 14396551867 ∧ LOG1E13LB ≤ gv 537 := by
  constructor
  · rw [Gv_eq_T 537 (by norm_num)]
    exact EqEv 25 (by norm_num)
  · rw [gv_eq_T 537 (by norm_num)]
    exact DnEv 25 (by norm_num)

theorem bnd_538 : Gv 538 = 14395604395 ∧ LOG1E13LB ≤ gv 538 := by
  constructor
  · rw [Gv_eq_T 538 (by norm_num)]
    exact EqEv 26 (by norm_num)
  · rw [gv_eq_T 538 (by norm_num)]
    exact DnEv 26 (by norm_num)

theorem bnd_539 : Gv 539 = 14394618535 ∧ LOG1E13LB ≤ gv 539 := by
  constructor
  · rw [Gv_eq_T 539 (by norm_num)]
    exact EqEv 27 (by norm_num)
  · rw [gv_eq_T 539 (by norm_num)]
    exact DnEv 27 (by norm_num)

theorem bnd_540 : Gv 540 = 14393594817 ∧ LOG1E13LB ≤ gv 540 := by
  constructor
  · rw [Gv_eq_T 540 (by norm_num)]
    exact EqEv 28 (by norm_num)
  · rw [gv_eq_T 540 (by norm_num)]
    exact DnEv 28 (by norm_num)

theorem bnd_541 : Gv 541 = 14392531217 ∧ LOG1E13LB ≤ gv 541 := by
  constructor
  · rw [Gv_eq_T 541 (by norm_num)]
    exact EqEv 29 (by norm_num)
  · rw [gv_eq_T 541 (by norm_num)]
    exact DnEv 29 (by norm_num)

theorem bnd_542 : Gv 542 = 14391429793 ∧ LOG1E13LB ≤ gv 542 := by
  constructor
  · rw [Gv_eq_T 542 (by norm_num)]
    exact EqEv 30 (by norm_num)
  · rw [gv_eq_T 542 (by norm_num)]
    exact DnEv 30 (by norm_num)

theorem bnd_543 : Gv 543 = 14390291635 ∧ LOG1E13LB ≤ gv 543 := by
  constructor
  · rw [Gv_eq_T 543 (by norm_num)]
    exact EqEv 31 (by norm_num)
  · rw [gv_eq_T 543 (by norm_num)]
    exact DnEv 31 (by norm_num)

theorem bnd_544 : Gv 544 = 14389107879 ∧ LOG1E13LB ≤ gv 544 := by
  constructor
  · rw [Gv_eq_T 544 (by norm_num)]
    exact EqEv 32 (by norm_num)
  · rw [gv_eq_T 544 (by norm_num)]
    exact DnEv 32 (by norm_num)

theorem bnd_545 : Gv 545 = 14387887805 ∧ LOG1E13LB ≤ gv 545 := by
  constructor
  · rw [Gv_eq_T 545 (by norm_num)]
    exact EqEv 33 (by norm_num)
  · rw [gv_eq_T 545 (by norm_num)]
    exact DnEv 33 (by norm_num)

theorem bnd_546 : Gv 546 = 14386628497 ∧ LOG1E13LB ≤ gv 546 := by
  constructor
  · rw [Gv_eq_T 546 (by norm_num)]
    exact EqEv 34 (by norm_num)
  · rw [gv_eq_T 546 (by norm_num)]
    exact DnEv 34 (by norm_num)

theorem bnd_547 : Gv 547 = 14385331777 ∧ LOG1E13LB ≤ gv 547 := by
  constructor
  · rw [Gv_eq_T 547 (by norm_num)]
    exact EqEv 35 (by norm_num)
  · rw [gv_eq_T 547 (by norm_num)]
    exact DnEv 35 (by norm_num)

theorem bnd_548 : Gv 548 = 14383989963 ∧ LOG1E13LB ≤ gv 548 := by
  constructor
  · rw [Gv_eq_T 548 (by norm_num)]
    exact EqEv 36 (by norm_num)
  · rw [gv_eq_T 548 (by norm_num)]
    exact DnEv 36 (by norm_num)

theorem bnd_549 : Gv 549 = 14382611287 ∧ LOG1E13LB ≤ gv 549 := by
  constructor
  · rw [Gv_eq_T 549 (by norm_num)]
    exact EqEv 37 (by norm_num)
  · rw [gv_eq_T 549 (by norm_num)]
    exact DnEv 37 (by norm_num)

theorem bnd_550 : Gv 550 = 14381191085 ∧ LOG1E13LB ≤ gv 550 := by
  constructor
  · rw [Gv_eq_T 550 (by norm_num)]
    exact EqEv 38 (by norm_num)
  · rw [gv_eq_T 550 (by norm_num)]
    exact DnEv 38 (by norm_num)

theorem bnd_551 : Gv 551 = 14379731085 ∧ LOG1E13LB ≤ gv 551 := by
  constructor
  · rw [Gv_eq_T 551 (by norm_num)]
    exact EqEv 39 (by norm_num)
  · rw [gv_eq_T 551 (by norm_num)]
    exact DnEv 39 (by norm_num)

theorem bnd_552 : Gv 552 = 14378231579 ∧ LOG1E13LB ≤ gv 552 := by
  constructor
  · rw [Gv_eq_T 552 (by norm_num)]
    exact EqEv 40 (by norm_num)
  · rw [gv_eq_T 552 (by norm_num)]
    exact DnEv 40 (by norm_num)

theorem bnd_553 : Gv 553 = 14376686909 ∧ LOG1E13LB ≤ gv 553 := by
  constructor
  · rw [Gv_eq_T 553 (by norm_num)]
    exact EqEv 41 (by norm_num)
  · rw [gv_eq_T 553 (by norm_num)]
    exact DnEv 41 (by norm_num)

theorem bnd_554 : Gv 554 = 14375105695 ∧ LOG1E13LB ≤ gv 554 := by
  constructor
  · rw [Gv_eq_T 554 (by norm_num)]
    exact EqEv 42 (by norm_num)
  · rw [gv_eq_T 554 (by norm_num)]
    exact DnEv 42 (by norm_num)

theorem bnd_555 : Gv 555 = 14373479381 ∧ LOG1E13LB ≤ gv 555 := by
  constructor
  · rw [Gv_eq_T 555 (by norm_num)]
    exact EqEv 43 (by norm_num)
  · rw [gv_eq_T 555 (by norm_num)]
    exact DnEv 43 (by norm_num)

theorem bnd_556 : Gv 556 = 14371811959 ∧ LOG1E13LB ≤ gv 556 := by
  constructor
  · rw [Gv_eq_T 556 (by norm_num)]
    exact EqEv 44 (by norm_num)
  · rw [gv_eq_T 556 (by norm_num)]
    exact DnEv 44 (by norm_num)

theorem bnd_557 : Gv 557 = 14370099787 ∧ LOG1E13LB ≤ gv 557 := by
  constructor
  · rw [Gv_eq_T 557 (by norm_num)]
    exact EqEv 45 (by norm_num)
  · rw [gv_eq_T 557 (by norm_num)]
    exact DnEv 45 (by norm_num)

theorem bnd_558 : Gv 558 = 14368346875 ∧ LOG1E13LB ≤ gv 558 := by
  constructor
  · rw [Gv_eq_T 558 (by norm_num)]
    exact EqEv 46 (by norm_num)
  · rw [gv_eq_T 558 (by norm_num)]
    exact DnEv 46 (by norm_num)

theorem bnd_559 : Gv 559 = 14366555243 ∧ LOG1E13LB ≤ gv 559 := by
  constructor
  · rw [Gv_eq_T 559 (by norm_num)]
    exact EqEv 47 (by norm_num)
  · rw [gv_eq_T 559 (by norm_num)]
    exact DnEv 47 (by norm_num)

theorem bnd_560 : Gv 560 = 14364712941 ∧ LOG1E13LB ≤ gv 560 := by
  constructor
  · rw [Gv_eq_T 560 (by norm_num)]
    exact EqEv 48 (by norm_num)
  · rw [gv_eq_T 560 (by norm_num)]
    exact DnEv 48 (by norm_num)

theorem bnd_561 : Gv 561 = 14362835193 ∧ LOG1E13LB ≤ gv 561 := by
  constructor
  · rw [Gv_eq_T 561 (by norm_num)]
    exact EqEv 49 (by norm_num)
  · rw [gv_eq_T 561 (by norm_num)]
    exact DnEv 49 (by norm_num)

theorem bnd_562 : Gv 562 = 14360910957 ∧ LOG1E13LB ≤ gv 562 := by
  constructor
  · rw [Gv_eq_T 562 (by norm_num)]
    exact EqEv 50 (by norm_num)
  · rw [gv_eq_T 562 (by norm_num)]
    exact DnEv 50 (by norm_num)

theorem bnd_563 : Gv 563 = 14358941713 ∧ LOG1E13LB ≤ gv 563 := by
  constructor
  · rw [Gv_eq_T 563 (by norm_num)]
    exact EqEv 51 (by norm_num)
  · rw [gv_eq_T 563 (by norm_num)]
    exact DnEv 51 (by norm_num)

theorem bnd_564 : Gv 564 = 14356928513 ∧ LOG1E13LB ≤ gv 564 := by
  constructor
  · rw [Gv_eq_T 564 (by norm_num)]
    exact EqEv 52 (by norm_num)
  · rw [gv_eq_T 564 (by norm_num)]
    exact DnEv 52 (by norm_num)

theorem bnd_565 : Gv 565 = 14354872269 ∧ LOG1E13LB ≤ gv 565 := by
  constructor
  · rw [Gv_eq_T 565 (by norm_num)]
    exact EqEv 53 (by norm_num)
  · rw [gv_eq_T 565 (by norm_num)]
    exact DnEv 53 (by norm_num)

theorem bnd_566 : Gv 566 = 14352769279 ∧ LOG1E13LB ≤ gv 566 := by
  constructor
  · rw [Gv_eq_T 566 (by norm_num)]
    exact EqEv 54 (by norm_num)
  · rw [gv_eq_T 566 (by norm_num)]
    exact DnEv 54 (by norm_num)

theorem bnd_567 : Gv 567 = 14350621945 ∧ LOG1E13LB ≤ gv 567 := by
  constructor
  · rw [Gv_eq_T 567 (by norm_num)]
    exact EqEv 55 (by norm_num)
  · rw [gv_eq_T 567 (by norm_num)]
    exact DnEv 55 (by norm_num)

theorem bnd_568 : Gv 568 = 14348429019 ∧ LOG1E13LB ≤ gv 568 := by
  constructor
  · rw [Gv_eq_T 568 (by norm_num)]
    exact EqEv 56 (by norm_num)
  · rw [gv_eq_T 568 (by norm_num)]
    exact DnEv 56 (by norm_num)

theorem bnd_569 : Gv 569 = 14346189193 ∧ LOG1E13LB ≤ gv 569 := by
  constructor
  · rw [Gv_eq_T 569 (by norm_num)]
    exact EqEv 57 (by norm_num)
  · rw [gv_eq_T 569 (by norm_num)]
    exact DnEv 57 (by norm_num)

theorem bnd_570 : Gv 570 = 14343904805 ∧ LOG1E13LB ≤ gv 570 := by
  constructor
  · rw [Gv_eq_T 570 (by norm_num)]
    exact EqEv 58 (by norm_num)
  · rw [gv_eq_T 570 (by norm_num)]
    exact DnEv 58 (by norm_num)

theorem bnd_571 : Gv 571 = 14341573437 ∧ LOG1E13LB ≤ gv 571 := by
  constructor
  · rw [Gv_eq_T 571 (by norm_num)]
    exact EqEv 59 (by norm_num)
  · rw [gv_eq_T 571 (by norm_num)]
    exact DnEv 59 (by norm_num)

theorem bnd_572 : Gv 572 = 14339197453 ∧ LOG1E13LB ≤ gv 572 := by
  constructor
  · rw [Gv_eq_T 572 (by norm_num)]
    exact EqEv 60 (by norm_num)
  · rw [gv_eq_T 572 (by norm_num)]
    exact DnEv 60 (by norm_num)

theorem bnd_573 : Gv 573 = 14336768053 ∧ LOG1E13LB ≤ gv 573 := by
  constructor
  · rw [Gv_eq_T 573 (by norm_num)]
    exact EqEv 61 (by norm_num)
  · rw [gv_eq_T 573 (by norm_num)]
    exact DnEv 61 (by norm_num)

theorem bnd_574 : Gv 574 = 14334294259 ∧ LOG1E13LB ≤ gv 574 := by
  constructor
  · rw [Gv_eq_T 574 (by norm_num)]
    exact EqEv 62 (by norm_num)
  · rw [gv_eq_T 574 (by norm_num)]
    exact DnEv 62 (by norm_num)

theorem bnd_575 : Gv 575 = 14331772957 ∧ LOG1E13LB ≤ gv 575 := by
  constructor
  · rw [Gv_eq_T 575 (by norm_num)]
    exact EqEv 63 (by norm_num)
  · rw [gv_eq_T 575 (by norm_num)]
    exact DnEv 63 (by norm_num)

theorem bnd_576 : Gv 576 = 14329202739 ∧ LOG1E13LB ≤ gv 576 := by
  constructor
  · rw [Gv_eq_T 576 (by norm_num)]
    exact EqEv 64 (by norm_num)
  · rw [gv_eq_T 576 (by norm_num)]
    exact DnEv 64 (by norm_num)

theorem bnd_577 : Gv 577 = 14326578119 ∧ LOG1E13LB ≤ gv 577 := by
  constructor
  · rw [Gv_eq_T 577 (by norm_num)]
    exact EqEv 65 (by norm_num)
  · rw [gv_eq_T 577 (by norm_num)]
    exact DnEv 65 (by norm_num)

theorem bnd_578 : Gv 578 = 14323911691 ∧ LOG1E13LB ≤ gv 578 := by
  constructor
  · rw [Gv_eq_T 578 (by norm_num)]
    exact EqEv 66 (by norm_num)
  · rw [gv_eq_T 578 (by norm_num)]
    exact DnEv 66 (by norm_num)

theorem bnd_579 : Gv 579 = 14321192617 ∧ LOG1E13LB ≤ gv 579 := by
  constructor
  · rw [Gv_eq_T 579 (by norm_num)]
    exact EqEv 67 (by norm_num)
  · rw [gv_eq_T 579 (by norm_num)]
    exact DnEv 67 (by norm_num)

theorem bnd_580 : Gv 580 = 14318426437 ∧ LOG1E13LB ≤ gv 580 := by
  constructor
  · rw [Gv_eq_T 580 (by norm_num)]
    exact EqEv 68 (by norm_num)
  · rw [gv_eq_T 580 (by norm_num)]
    exact DnEv 68 (by norm_num)

theorem bnd_581 : Gv 581 = 14315603027 ∧ LOG1E13LB ≤ gv 581 := by
  constructor
  · rw [Gv_eq_T 581 (by norm_num)]
    exact EqEv 69 (by norm_num)
  · rw [gv_eq_T 581 (by norm_num)]
    exact DnEv 69 (by norm_num)

theorem bnd_582 : Gv 582 = 14312730103 ∧ LOG1E13LB ≤ gv 582 := by
  constructor
  · rw [Gv_eq_T 582 (by norm_num)]
    exact EqEv 70 (by norm_num)
  · rw [gv_eq_T 582 (by norm_num)]
    exact DnEv 70 (by norm_num)

theorem bnd_583 : Gv 583 = 14309806473 ∧ LOG1E13LB ≤ gv 583 := by
  constructor
  · rw [Gv_eq_T 583 (by norm_num)]
    exact EqEv 71 (by norm_num)
  · rw [gv_eq_T 583 (by norm_num)]
    exact DnEv 71 (by norm_num)

theorem bnd_584 : Gv 584 = 14306830721 ∧ LOG1E13LB ≤ gv 584 := by
  constructor
  · rw [Gv_eq_T 584 (by norm_num)]
    exact EqEv 72 (by norm_num)
  · rw [gv_eq_T 584 (by norm_num)]
    exact DnEv 72 (by norm_num)

theorem bnd_585 : Gv 585 = 14303800181 ∧ LOG1E13LB ≤ gv 585 := by
  constructor
  · rw [Gv_eq_T 585 (by norm_num)]
    exact EqEv 73 (by norm_num)
  · rw [gv_eq_T 585 (by norm_num)]
    exact DnEv 73 (by norm_num)

theorem bnd_586 : Gv 586 = 14300716931 ∧ LOG1E13LB ≤ gv 586 := by
  constructor
  · rw [Gv_eq_T 586 (by norm_num)]
    exact EqEv 74 (by norm_num)
  · rw [gv_eq_T 586 (by norm_num)]
    exact DnEv 74 (by norm_num)

theorem bnd_587 : Gv 587 = 14297580463 ∧ LOG1E13LB ≤ gv 587 := by
  constructor
  · rw [Gv_eq_T 587 (by norm_num)]
    exact EqEv 75 (by norm_num)
  · rw [gv_eq_T 587 (by norm_num)]
    exact DnEv 75 (by norm_num)

theorem bnd_588 : Gv 588 = 14294389165 ∧ LOG1E13LB ≤ gv 588 := by
  constructor
  · rw [Gv_eq_T 588 (by norm_num)]
    exact EqEv 76 (by norm_num)
  · rw [gv_eq_T 588 (by norm_num)]
    exact DnEv 76 (by norm_num)

theorem bnd_589 : Gv 589 = 14291142713 ∧ LOG1E13LB ≤ gv 589 := by
  constructor
  · rw [Gv_eq_T 589 (by norm_num)]
    exact EqEv 77 (by norm_num)
  · rw [gv_eq_T 589 (by norm_num)]
    exact DnEv 77 (by norm_num)

theorem bnd_590 : Gv 590 = 14287841547 ∧ LOG1E13LB ≤ gv 590 := by
  constructor
  · rw [Gv_eq_T 590 (by norm_num)]
    exact EqEv 78 (by norm_num)
  · rw [gv_eq_T 590 (by norm_num)]
    exact DnEv 78 (by norm_num)

theorem bnd_591 : Gv 591 = 14284487085 ∧ LOG1E13LB ≤ gv 591 := by
  constructor
  · rw [Gv_eq_T 591 (by norm_num)]
    exact EqEv 79 (by norm_num)
  · rw [gv_eq_T 591 (by norm_num)]
    exact DnEv 79 (by norm_num)

theorem bnd_592 : Gv 592 = 14281069793 ∧ LOG1E13LB ≤ gv 592 := by
  constructor
  · rw [Gv_eq_T 592 (by norm_num)]
    exact EqEv 80 (by norm_num)
  · rw [gv_eq_T 592 (by norm_num)]
    exact DnEv 80 (by norm_num)

theorem bnd_593 : Gv 593 = 14277597643 ∧ LOG1E13LB ≤ gv 593 := by
  constructor
  · rw [Gv_eq_T 593 (by norm_num)]
    exact EqEv 81 (by norm_num)
  · rw [gv_eq_T 593 (by norm_num)]
    exact DnEv 81 (by norm_num)

theorem bnd_594 : Gv 594 = 14274066495 ∧ LOG1E13LB ≤ gv 594 := by
  constructor
  · rw [Gv_eq_T 594 (by norm_num)]
    exact EqEv 82 (by norm_num)
  · rw [gv_eq_T 594 (by norm_num)]
    exact DnEv 82 (by norm_num)

theorem bnd_595 : Gv 595 = 14270475661 ∧ LOG1E13LB ≤ gv 595 := by
  constructor
  · rw [Gv_eq_T 595 (by norm_num)]
    exact EqEv 83 (by norm_num)
  · rw [gv_eq_T 595 (by norm_num)]
    exact DnEv 83 (by norm_num)

theorem bnd_596 : Gv 596 = 14266828709 ∧ LOG1E13LB ≤ gv 596 := by
  constructor
  · rw [Gv_eq_T 596 (by norm_num)]
    exact EqEv 84 (by norm_num)
  · rw [gv_eq_T 596 (by norm_num)]
    exact DnEv 84 (by norm_num)

theorem bnd_597 : Gv 597 = 14263121703 ∧ LOG1E13LB ≤ gv 597 := by
  constructor
  · rw [Gv_eq_T 597 (by norm_num)]
    exact EqEv 85 (by norm_num)
  · rw [gv_eq_T 597 (by norm_num)]
    exact DnEv 85 (by norm_num)

theorem bnd_598 : Gv 598 = 14259349687 ∧ LOG1E13LB ≤ gv 598 := by
  constructor
  · rw [Gv_eq_T 598 (by norm_num)]
    exact EqEv 86 (by norm_num)
  · rw [gv_eq_T 598 (by norm_num)]
    exact DnEv 86 (by norm_num)

theorem bnd_599 : Gv 599 = 14255521059 ∧ LOG1E13LB ≤ gv 599 := by
  constructor
  · rw [Gv_eq_T 599 (by norm_num)]
    exact EqEv 87 (by norm_num)
  · rw [gv_eq_T 599 (by norm_num)]
    exact DnEv 87 (by norm_num)

theorem bnd_600 : Gv 600 = 14251631935 ∧ LOG1E13LB ≤ gv 600 := by
  constructor
  · rw [Gv_eq_T 600 (by norm_num)]
    exact EqEv 88 (by norm_num)
  · rw [gv_eq_T 600 (by norm_num)]
    exact DnEv 88 (by norm_num)

theorem bnd_601 : Gv 601 = 14247674803 ∧ LOG1E13LB ≤ gv 601 := by
  constructor
  · rw [Gv_eq_T 601 (by norm_num)]
    exact EqEv 89 (by norm_num)
  · rw [gv_eq_T 601 (by norm_num)]
    exact DnEv 89 (by norm_num)

theorem bnd_602 : Gv 602 = 14243654989 ∧ LOG1E13LB ≤ gv 602 := by
  constructor
  · rw [Gv_eq_T 602 (by norm_num)]
    exact EqEv 90 (by norm_num)
  · rw [gv_eq_T 602 (by norm_num)]
    exact DnEv 90 (by norm_num)

theorem bnd_603 : Gv 603 = 14239574209 ∧ LOG1E13LB ≤ gv 603 := by
  constructor
  · rw [Gv_eq_T 603 (by norm_num)]
    exact EqEv 91 (by norm_num)
  · rw [gv_eq_T 603 (by norm_num)]
    exact DnEv 91 (by norm_num)

theorem bnd_604 : Gv 604 = 14235426477 ∧ LOG1E13LB ≤ gv 604 := by
  constructor
  · rw [Gv_eq_T 604 (by norm_num)]
    exact EqEv 92 (by norm_num)
  · rw [gv_eq_T 604 (by norm_num)]
    exact DnEv 92 (by norm_num)

theorem bnd_605 : Gv 605 = 14231210859 ∧ LOG1E13LB ≤ gv 605 := by
  constructor
  · rw [Gv_eq_T 605 (by norm_num)]
    exact EqEv 93 (by norm_num)
  · rw [gv_eq_T 605 (by norm_num)]
    exact DnEv 93 (by norm_num)

theorem bnd_606 : Gv 606 = 14226932143 ∧ LOG1E13LB ≤ gv 606 := by
  constructor
  · rw [Gv_eq_T 606 (by norm_num)]
    exact EqEv 94 (by norm_num)
  · rw [gv_eq_T 606 (by norm_num)]
    exact DnEv 94 (by norm_num)

theorem bnd_607 : Gv 607 = 14222584873 ∧ LOG1E13LB ≤ gv 607 := by
  constructor
  · rw [Gv_eq_T 607 (by norm_num)]
    exact EqEv 95 (by norm_num)
  · rw [gv_eq_T 607 (by norm_num)]
    exact DnEv 95 (by norm_num)

theorem bnd_608 : Gv 608 = 14218167501 ∧ LOG1E13LB ≤ gv 608 := by
  constructor
  · rw [Gv_eq_T 608 (by norm_num)]
    exact EqEv 96 (by norm_num)
  · rw [gv_eq_T 608 (by norm_num)]
    exact DnEv 96 (by norm_num)

theorem bnd_609 : Gv 609 = 14213684151 ∧ LOG1E13LB ≤ gv 609 := by
  constructor
  · rw [Gv_eq_T 609 (by norm_num)]
    exact EqEv 97 (by norm_num)
  · rw [gv_eq_T 609 (by norm_num)]
    exact DnEv 97 (by norm_num)

theorem bnd_610 : Gv 610 = 14209127163 ∧ LOG1E13LB ≤ gv 610 := by
  constructor
  · rw [Gv_eq_T 610 (by norm_num)]
    exact EqEv 98 (by norm_num)
  · rw [gv_eq_T 610 (by norm_num)]
    exact DnEv 98 (by norm_num)

theorem bnd_611 : Gv 611 = 14204502003 ∧ LOG1E13LB ≤ gv 611 := by
  constructor
  · rw [Gv_eq_T 611 (by norm_num)]
    exact EqEv 99 (by norm_num)
  · rw [gv_eq_T 611 (by norm_num)]
    exact DnEv 99 (by norm_num)

theorem bnd_612 : Gv 612 = 14199804723 ∧ LOG1E13LB ≤ gv 612 := by
  constructor
  · rw [Gv_eq_T 612 (by norm_num)]
    exact EqEv 100 (by norm_num)
  · rw [gv_eq_T 612 (by norm_num)]
    exact DnEv 100 (by norm_num)

theorem bnd_613 : Gv 613 = 14195034487 ∧ LOG1E13LB ≤ gv 613 := by
  constructor
  · rw [Gv_eq_T 613 (by norm_num)]
    exact EqEv 101 (by norm_num)
  · rw [gv_eq_T 613 (by norm_num)]
    exact DnEv 101 (by norm_num)

theorem bnd_614 : Gv 614 = 14190191381 ∧ LOG1E13LB ≤ gv 614 := by
  constructor
  · rw [Gv_eq_T 614 (by norm_num)]
    exact EqEv 102 (by norm_num)
  · rw [gv_eq_T 614 (by norm_num)]
    exact DnEv 102 (by norm_num)

theorem bnd_615 : Gv 615 = 14185273443 ∧ LOG1E13LB ≤ gv 615 := by
  constructor
  · rw [Gv_eq_T 615 (by norm_num)]
    exact EqEv 103 (by norm_num)
  · rw [gv_eq_T 615 (by norm_num)]
    exact DnEv 103 (by norm_num)

theorem bnd_616 : Gv 616 = 14180279823 ∧ LOG1E13LB ≤ gv 616 := by
  constructor
  · rw [Gv_eq_T 616 (by norm_num)]
    exact EqEv 104 (by norm_num)
  · rw [gv_eq_T 616 (by norm_num)]
    exact DnEv 104 (by norm_num)

theorem bnd_617 : Gv 617 = 14175209443 ∧ LOG1E13LB ≤ gv 617 := by
  constructor
  · rw [Gv_eq_T 617 (by norm_num)]
    exact EqEv 105 (by norm_num)
  · rw [gv_eq_T 617 (by norm_num)]
    exact DnEv 105 (by norm_num)

theorem bnd_618 : Gv 618 = 14170067483 ∧ LOG1E13LB ≤ gv 618 := by
  constructor
  · rw [Gv_eq_T 618 (by norm_num)]
    exact EqEv 106 (by norm_num)
  · rw [gv_eq_T 618 (by norm_num)]
    exact DnEv 106 (by norm_num)

theorem bnd_619 : Gv 619 = 14164832917 ∧ LOG1E13LB ≤ gv 619 := by
  constructor
  · rw [Gv_eq_T 619 (by norm_num)]
    exact EqEv 107 (by norm_num)
  · rw [gv_eq_T 619 (by norm_num)]
    exact DnEv 107 (by norm_num)

theorem bnd_620 : Gv 620 = 14159526587 ∧ LOG1E13LB ≤ gv 620 := by
  constructor
  · rw [Gv_eq_T 620 (by norm_num)]
    exact EqEv 108 (by norm_num)
  · rw [gv_eq_T 620 (by norm_num)]
    exact DnEv 108 (by norm_num)

theorem bnd_621 : Gv 621 = 14154144709 ∧ LOG1E13LB ≤ gv 621 := by
  constructor
  · rw [Gv_eq_T 621 (by norm_num)]
    exact EqEv 109 (by norm_num)
  · rw [gv_eq_T 621 (by norm_num)]
    exact DnEv 109 (by norm_num)

theorem bnd_622 : Gv 622 = 14148672619 ∧ LOG1E13LB ≤ gv 622 := by
  constructor
  · rw [Gv_eq_T 622 (by norm_num)]
    exact EqEv 110 (by norm_num)
  · rw [gv_eq_T 622 (by norm_num)]
    exact DnEv 110 (by norm_num)

theorem bnd_623 : Gv 623 = 14143124333 ∧ LOG1E13LB ≤ gv 623 := by
  constructor
  · rw [Gv_eq_T 623 (by norm_num)]
    exact EqEv 111 (by norm_num)
  · rw [gv_eq_T 623 (by norm_num)]
    exact DnEv 111 (by norm_num)

theorem bnd_624 : Gv 624 = 14137484473 ∧ LOG1E13LB ≤ gv 624 := by
  constructor
  · rw [Gv_eq_T 624 (by norm_num)]
    exact EqEv 112 (by norm_num)
  · rw [gv_eq_T 624 (by norm_num)]
    exact DnEv 112 (by norm_num)

theorem bnd_625 : Gv 625 = 14131765697 ∧ LOG1E13LB ≤ gv 625 := by
  constructor
  · rw [Gv_eq_T 625 (by norm_num)]
    exact EqEv 113 (by norm_num)
  · rw [gv_eq_T 625 (by norm_num)]
    exact DnEv 113 (by norm_num)

theorem bnd_626 : Gv 626 = 14125954977 ∧ LOG1E13LB ≤ gv 626 := by
  constructor
  · rw [Gv_eq_T 626 (by norm_num)]
    exact EqEv 114 (by norm_num)
  · rw [gv_eq_T 626 (by norm_num)]
    exact DnEv 114 (by norm_num)

theorem bnd_627 : Gv 627 = 14120056867 ∧ LOG1E13LB ≤ gv 627 := by
  constructor
  · rw [Gv_eq_T 627 (by norm_num)]
    exact EqEv 115 (by norm_num)
  · rw [gv_eq_T 627 (by norm_num)]
    exact DnEv 115 (by norm_num)

theorem bnd_628 : Gv 628 = 14114072033 ∧ LOG1E13LB ≤ gv 628 := by
  constructor
  · rw [Gv_eq_T 628 (by norm_num)]
    exact EqEv 116 (by norm_num)
  · rw [gv_eq_T 628 (by norm_num)]
    exact DnEv 116 (by norm_num)

theorem bnd_629 : Gv 629 = 14107996451 ∧ LOG1E13LB ≤ gv 629 := by
  constructor
  · rw [Gv_eq_T 629 (by norm_num)]
    exact EqEv 117 (by norm_num)
  · rw [gv_eq_T 629 (by norm_num)]
    exact DnEv 117 (by norm_num)

theorem bnd_630 : Gv 630 = 14101830461 ∧ LOG1E13LB ≤ gv 630 := by
  constructor
  · rw [Gv_eq_T 630 (by norm_num)]
    exact EqEv 118 (by norm_num)
  · rw [gv_eq_T 630 (by norm_num)]
    exact DnEv 118 (by norm_num)

theorem bnd_631 : Gv 631 = 14095568655 ∧ LOG1E13LB ≤ gv 631 := by
  constructor
  · rw [Gv_eq_T 631 (by norm_num)]
    exact EqEv 119 (by norm_num)
  · rw [gv_eq_T 631 (by norm_num)]
    exact DnEv 119 (by norm_num)

theorem bnd_632 : Gv 632 = 14089218905 ∧ LOG1E13LB ≤ gv 632 := by
  constructor
  · rw [Gv_eq_T 632 (by norm_num)]
    exact EqEv 120 (by norm_num)
  · rw [gv_eq_T 632 (by norm_num)]
    exact DnEv 120 (by norm_num)

theorem bnd_633 : Gv 633 = 14082762097 ∧ LOG1E13LB ≤ gv 633 := by
  constructor
  · rw [Gv_eq_T 633 (by norm_num)]
    exact EqEv 121 (by norm_num)
  · rw [gv_eq_T 633 (by norm_num)]
    exact DnEv 121 (by norm_num)

theorem bnd_634 : Gv 634 = 14076218235 ∧ LOG1E13LB ≤ gv 634 := by
  constructor
  · rw [Gv_eq_T 634 (by norm_num)]
    exact EqEv 122 (by norm_num)
  · rw [gv_eq_T 634 (by norm_num)]
    exact DnEv 122 (by norm_num)

theorem bnd_635 : Gv 635 = 14069568383 ∧ LOG1E13LB ≤ gv 635 := by
  constructor
  · rw [Gv_eq_T 635 (by norm_num)]
    exact EqEv 123 (by norm_num)
  · rw [gv_eq_T 635 (by norm_num)]
    exact DnEv 123 (by norm_num)

theorem bnd_636 : Gv 636 = 14062823763 ∧ LOG1E13LB ≤ gv 636 := by
  constructor
  · rw [Gv_eq_T 636 (by norm_num)]
    exact EqEv 124 (by norm_num)
  · rw [gv_eq_T 636 (by norm_num)]
    exact DnEv 124 (by norm_num)

theorem bnd_637 : Gv 637 = 14055969925 ∧ LOG1E13LB ≤ gv 637 := by
  constructor
  · rw [Gv_eq_T 637 (by norm_num)]
    exact EqEv 125 (by norm_num)
  · rw [gv_eq_T 637 (by norm_num)]
    exact DnEv 125 (by norm_num)

theorem bnd_638 : Gv 638 = 14049018173 ∧ LOG1E13LB ≤ gv 638 := by
  constructor
  · rw [Gv_eq_T 638 (by norm_num)]
    exact EqEv 126 (by norm_num)
  · rw [gv_eq_T 638 (by norm_num)]
    exact DnEv 126 (by norm_num)

theorem bnd_639 : Gv 639 = 14041961725 ∧ LOG1E13LB ≤ gv 639 := by
  constructor
  · rw [Gv_eq_T 639 (by norm_num)]
    exact EqEv 127 (by norm_num)
  · rw [gv_eq_T 639 (by norm_num)]
    exact DnEv 127 (by norm_num)

theorem bnd_640 : Gv 640 = 14034795785 ∧ LOG1E13LB ≤ gv 640 := by
  constructor
  · rw [Gv_eq_T 640 (by norm_num)]
    exact EqFv 0 (by norm_num)
  · rw [gv_eq_T 640 (by norm_num)]
    exact DnFv 0 (by norm_num)

theorem bnd_641 : Gv 641 = 14027520647 ∧ LOG1E13LB ≤ gv 641 := by
  constructor
  · rw [Gv_eq_T 641 (by norm_num)]
    exact EqFv 1 (by norm_num)
  · rw [gv_eq_T 641 (by norm_num)]
    exact DnFv 1 (by norm_num)

theorem bnd_642 : Gv 642 = 14020139299 ∧ LOG1E13LB ≤ gv 642 := by
  constructor
  · rw [Gv_eq_T 642 (by norm_num)]
    exact EqFv 2 (by norm_num)
  · rw [gv_eq_T 642 (by norm_num)]
    exact DnFv 2 (by norm_num)

theorem bnd_643 : Gv 643 = 14012643897 ∧ LOG1E13LB ≤ gv 643 := by
  constructor
  · rw [Gv_eq_T 643 (by norm_num)]
    exact EqFv 3 (by norm_num)
  · rw [gv_eq_T 643 (by norm_num)]
    exact DnFv 3 (by norm_num)

theorem bnd_644 : Gv 644 = 14005034075 ∧ LOG1E13LB ≤ gv 644 := by
  constructor
  · rw [Gv_eq_T 644 (by norm_num)]
    exact EqFv 4 (by norm_num)
  · rw [gv_eq_T 644 (by norm_num)]
    exact DnFv 4 (by norm_num)

theorem bnd_645 : Gv 645 = 13997309851 ∧ LOG1E13LB ≤ gv 645 := by
  constructor
  · rw [Gv_eq_T 645 (by norm_num)]
    exact EqFv 5 (by norm_num)
  · rw [gv_eq_T 645 (by norm_num)]
    exact DnFv 5 (by norm_num)

theorem bnd_646 : Gv 646 = 13989466089 ∧ LOG1E13LB ≤ gv 646 := by
  constructor
  · rw [Gv_eq_T 646 (by norm_num)]
    exact EqFv 6 (by norm_num)
  · rw [gv_eq_T 646 (by norm_num)]
    exact DnFv 6 (by norm_num)

theorem bnd_647 : Gv 647 = 13981501371 ∧ LOG1E13LB ≤ gv 647 := by
  constructor
  · rw [Gv_eq_T 647 (by norm_num)]
    exact EqFv 7 (by norm_num)
  · rw [gv_eq_T 647 (by norm_num)]
    exact DnFv 7 (by norm_num)

theorem bnd_648 : Gv 648 = 13973419765 ∧ LOG1E13LB ≤ gv 648 := by
  constructor
  · rw [Gv_eq_T 648 (by norm_num)]
    exact EqFv 8 (by norm_num)
  · rw [gv_eq_T 648 (by norm_num)]
    exact DnFv 8 (by norm_num)

theorem bnd_649 : Gv 649 = 13965212501 ∧ LOG1E13LB ≤ gv 649 := by
  constructor
  · rw [Gv_eq_T 649 (by norm_num)]
    exact EqFv 9 (by norm_num)
  · rw [gv_eq_T 649 (by norm_num)]
    exact DnFv 9 (by norm_num)

theorem bnd_650 : Gv 650 = 13956878995 ∧ LOG1E13LB ≤ gv 650 := by
  constructor
  · rw [Gv_eq_T 650 (by norm_num)]
    exact EqFv 10 (by norm_num)
  · rw [gv_eq_T 650 (by norm_num)]
    exact DnFv 10 (by norm_num)

theorem bnd_651 : Gv 651 = 13948417251 ∧ LOG1E13LB ≤ gv 651 := by
  constructor
  · rw [Gv_eq_T 651 (by norm_num)]
    exact EqFv 11 (by norm_num)
  · rw [gv_eq_T 651 (by norm_num)]
    exact DnFv 11 (by norm_num)

theorem bnd_652 : Gv 652 = 13939823735 ∧ LOG1E13LB ≤ gv 652 := by
  constructor
  · rw [Gv_eq_T 652 (by norm_num)]
    exact EqFv 12 (by norm_num)
  · rw [gv_eq_T 652 (by norm_num)]
    exact DnFv 12 (by norm_num)

theorem bnd_653 : Gv 653 = 13931100365 ∧ LOG1E13LB ≤ gv 653 := by
  constructor
  · rw [Gv_eq_T 653 (by norm_num)]
    exact EqFv 13 (by norm_num)
  · rw [gv_eq_T 653 (by norm_num)]
    exact DnFv 13 (by norm_num)

theorem bnd_654 : Gv 654 = 13922245235 ∧ LOG1E13LB ≤ gv 654 := by
  constructor
  · rw [Gv_eq_T 654 (by norm_num)]
    exact EqFv 14 (by norm_num)
  · rw [gv_eq_T 654 (by norm_num)]
    exact DnFv 14 (by norm_num)

theorem bnd_655 : Gv 655 = 13913250857 ∧ LOG1E13LB ≤ gv 655 := by
  constructor
  · rw [Gv_eq_T 655 (by norm_num)]
    exact EqFv 15 (by norm_num)
  · rw [gv_eq_T 655 (by norm_num)]
    exact DnFv 15 (by norm_num)

theorem bnd_656 : Gv 656 = 13904113965 ∧ LOG1E13LB ≤ gv 656 := by
  constructor
  · rw [Gv_eq_T 656 (by norm_num)]
    exact EqFv 16 (by norm_num)
  · rw [gv_eq_T 656 (by norm_num)]
    exact DnFv 16 (by norm_num)

theorem bnd_657 : Gv 657 = 13894837277 ∧ LOG1E13LB ≤ gv 657 := by
  constructor
  · rw [Gv_eq_T 657 (by norm_num)]
    exact EqFv 17 (by norm_num)
  · rw [gv_eq_T 657 (by norm_num)]
    exact DnFv 17 (by norm_num)

theorem bnd_658 : Gv 658 = 13885419591 ∧ LOG1E13LB ≤ gv 658 := by
  constructor
  · rw [Gv_eq_T 658 (by norm_num)]
    exact EqFv 18 (by norm_num)
  · rw [gv_eq_T 658 (by norm_num)]
    exact DnFv 18 (by norm_num)

theorem bnd_659 : Gv 659 = 13875852035 ∧ LOG1E13LB ≤ gv 659 := by
  constructor
  · rw [Gv_eq_T 659 (by norm_num)]
    exact EqFv 19 (by norm_num)
  · rw [gv_eq_T 659 (by norm_num)]
    exact DnFv 19 (by norm_num)

theorem bnd_660 : Gv 660 = 13866136665 ∧ LOG1E13LB ≤ gv 660 := by
  constructor
  · rw [Gv_eq_T 660 (by norm_num)]
    exact EqFv 20 (by norm_num)
  · rw [gv_eq_T 660 (by norm_num)]
    exact DnFv 20 (by norm_num)

theorem bnd_661 : Gv 661 = 13856265659 ∧ LOG1E13LB ≤ gv 661 := by
  constructor
  · rw [Gv_eq_T 661 (by norm_num)]
    exact EqFv 21 (by norm_num)
  · rw [gv_eq_T 661 (by norm_num)]
    exact DnFv 21 (by norm_num)

theorem bnd_662 : Gv 662 = 13846238683 ∧ LOG1E13LB ≤ gv 662 := by
  constructor
  · rw [Gv_eq_T 662 (by norm_num)]
    exact EqFv 22 (by norm_num)
  · rw [gv_eq_T 662 (by norm_num)]
    exact DnFv 22 (by norm_num)

theorem bnd_663 : Gv 663 = 13836058357 ∧ LOG1E13LB ≤ gv 663 := by
  constructor
  · rw [Gv_eq_T 663 (by norm_num)]
    exact EqFv 23 (by norm_num)
  · rw [gv_eq_T 663 (by norm_num)]
    exact DnFv 23 (by norm_num)

theorem bnd_664 : Gv 664 = 13825712627 ∧ LOG1E13LB ≤ gv 664 := by
  constructor
  · rw [Gv_eq_T 664 (by norm_num)]
    exact EqFv 24 (by norm_num)
  · rw [gv_eq_T 664 (by norm_num)]
    exact DnFv 24 (by norm_num)

theorem bnd_665 : Gv 665 = 13815207699 ∧ LOG1E13LB ≤ gv 665 := by
  constructor
  · rw [Gv_eq_T 665 (by norm_num)]
    exact EqFv 25 (by norm_num)
  · rw [gv_eq_T 665 (by norm_num)]
    exact DnFv 25 (by norm_num)

theorem bnd_666 : Gv 666 = 13804531623 ∧ LOG1E13LB ≤ gv 666 := by
  constructor
  · rw [Gv_eq_T 666 (by norm_num)]
    exact EqFv 26 (by norm_num)
  · rw [gv_eq_T 666 (by norm_num)]
    exact DnFv 26 (by norm_num)

theorem bnd_667 : Gv 667 = 13793685901 ∧ LOG1E13LB ≤ gv 667 := by
  constructor
  · rw [Gv_eq_T 667 (by norm_num)]
    exact EqFv 27 (by norm_num)
  · rw [gv_eq_T 667 (by norm_num)]
    exact DnFv 27 (by norm_num)

theorem bnd_668 : Gv 668 = 13782664959 ∧ LOG1E13LB ≤ gv 668 := by
  constructor
  · rw [Gv_eq_T 668 (by norm_num)]
    exact EqFv 28 (by norm_num)
  · rw [gv_eq_T 668 (by norm_num)]
    exact DnFv 28 (by norm_num)

theorem bnd_669 : Gv 669 = 13771470325 ∧ LOG1E13LB ≤ gv 669 := by
  constructor
  · rw [Gv_eq_T 669 (by norm_num)]
    exact EqFv 29 (by norm_num)
  · rw [gv_eq_T 669 (by norm_num)]
    exact DnFv 29 (by norm_num)

theorem bnd_670 : Gv 670 = 13760098737 ∧ LOG1E13LB ≤ gv 670 := by
  constructor
  · rw [Gv_eq_T 670 (by norm_num)]
    exact EqFv 30 (by norm_num)
  · rw [gv_eq_T 670 (by norm_num)]
    exact DnFv 30 (by norm_num)

theorem bnd_671 : Gv 671 = 13748532409 ∧ LOG1E13LB ≤ gv 671 := by
  constructor
  · rw [Gv_eq_T 671 (by norm_num)]
    exact EqFv 31 (by norm_num)
  · rw [gv_eq_T 671 (by norm_num)]
    exact DnFv 31 (by norm_num)

theorem bnd_672 : Gv 672 = 13736784461 ∧ LOG1E13LB ≤ gv 672 := by
  constructor
  · rw [Gv_eq_T 672 (by norm_num)]
    exact EqFv 32 (by norm_num)
  · rw [gv_eq_T 672 (by norm_num)]
    exact DnFv 32 (by norm_num)

theorem bnd_673 : Gv 673 = 13724843891 ∧ LOG1E13LB ≤ gv 673 := by
  constructor
  · rw [Gv_eq_T 673 (by norm_num)]
    exact EqFv 33 (by norm_num)
  · rw [gv_eq_T 673 (by norm_num)]
    exact DnFv 33 (by norm_num)

theorem bnd_674 : Gv 674 = 13712708685 ∧ LOG1E13LB ≤ gv 674 := by
  constructor
  · rw [Gv_eq_T 674 (by norm_num)]
    exact EqFv 34 (by norm_num)
  · rw [gv_eq_T 674 (by norm_num)]
    exact DnFv 34 (by norm_num)

theorem bnd_675 : Gv 675 = 13700374731 ∧ LOG1E13LB ≤ gv 675 := by
  constructor
  · rw [Gv_eq_T 675 (by norm_num)]
    exact EqFv 35 (by norm_num)
  · rw [gv_eq_T 675 (by norm_num)]
    exact DnFv 35 (by norm_num)

theorem bnd_676 : Gv 676 = 13687836275 ∧ LOG1E13LB ≤ gv 676 := by
  constructor
  · rw [Gv_eq_T 676 (by norm_num)]
    exact EqFv 36 (by norm_num)
  · rw [gv_eq_T 676 (by norm_num)]
    exact DnFv 36 (by norm_num)

theorem bnd_677 : Gv 677 = 13675088943 ∧ LOG1E13LB ≤ gv 677 := by
  constructor
  · rw [Gv_eq_T 677 (by norm_num)]
    exact EqFv 37 (by norm_num)
  · rw [gv_eq_T 677 (by norm_num)]
    exact DnFv 37 (by norm_num)

theorem bnd_678 : Gv 678 = 13662131409 ∧ LOG1E13LB ≤ gv 678 := by
  constructor
  · rw [Gv_eq_T 678 (by norm_num)]
    exact EqFv 38 (by norm_num)
  · rw [gv_eq_T 678 (by norm_num)]
    exact DnFv 38 (by norm_num)

theorem bnd_679 : Gv 679 = 13648957587 ∧ LOG1E13LB ≤ gv 679 := by
  constructor
  · rw [Gv_eq_T 679 (by norm_num)]
    exact EqFv 39 (by norm_num)
  · rw [gv_eq_T 679 (by norm_num)]
    exact DnFv 39 (by norm_num)

theorem bnd_680 : Gv 680 = 13635561469 ∧ LOG1E13LB ≤ gv 680 := by
  constructor
  · rw [Gv_eq_T 680 (by norm_num)]
    exact EqFv 40 (by norm_num)
  · rw [gv_eq_T 680 (by norm_num)]
    exact DnFv 40 (by norm_num)

theorem bnd_681 : Gv 681 = 13621942045 ∧ LOG1E13LB ≤ gv 681 := by
  constructor
  · rw [Gv_eq_T 681 (by norm_num)]
    exact EqFv 41 (by norm_num)
  · rw [gv_eq_T 681 (by norm_num)]
    exact DnFv 41 (by norm_num)

theorem bnd_682 : Gv 682 = 13608087601 ∧ LOG1E13LB ≤ gv 682 := by
  constructor
  · rw [Gv_eq_T 682 (by norm_num)]
    exact EqFv 42 (by norm_num)
  · rw [gv_eq_T 682 (by norm_num)]
    exact DnFv 42 (by norm_num)

theorem bnd_683 : Gv 683 = 13594000103 ∧ LOG1E13LB ≤ gv 683 := by
  constructor
  · rw [Gv_eq_T 683 (by norm_num)]
    exact EqFv 43 (by norm_num)
  · rw [gv_eq_T 683 (by norm_num)]
    exact DnFv 43 (by norm_num)

theorem bnd_684 : Gv 684 = 13579670783 ∧ LOG1E13LB ≤ gv 684 := by
  constructor
  · rw [Gv_eq_T 684 (by norm_num)]
    exact EqFv 44 (by norm_num)
  · rw [gv_eq_T 684 (by norm_num)]
    exact DnFv 44 (by norm_num)

theorem bnd_685 : Gv 685 = 13565097059 ∧ LOG1E13LB ≤ gv 685 := by
  constructor
  · rw [Gv_eq_T 685 (by norm_num)]
    exact EqFv 45 (by norm_num)
  · rw [gv_eq_T 685 (by norm_num)]
    exact DnFv 45 (by norm_num)

theorem bnd_686 : Gv 686 = 13550268705 ∧ LOG1E13LB ≤ gv 686 := by
  constructor
  · rw [Gv_eq_T 686 (by norm_num)]
    exact EqFv 46 (by norm_num)
  · rw [gv_eq_T 686 (by norm_num)]
    exact DnFv 46 (by norm_num)

theorem bnd_687 : Gv 687 = 13535185117 ∧ LOG1E13LB ≤ gv 687 := by
  constructor
  · rw [Gv_eq_T 687 (by norm_num)]
    exact EqFv 47 (by norm_num)
  · rw [gv_eq_T 687 (by norm_num)]
    exact DnFv 47 (by norm_num)

theorem bnd_688 : Gv 688 = 13519838251 ∧ LOG1E13LB ≤ gv 688 := by
  constructor
  · rw [Gv_eq_T 688 (by norm_num)]
    exact EqFv 48 (by norm_num)
  · rw [gv_eq_T 688 (by norm_num)]
    exact DnFv 48 (by norm_num)

theorem bnd_689 : Gv 689 = 13504223993 ∧ LOG1E13LB ≤ gv 689 := by
  constructor
  · rw [Gv_eq_T 689 (by norm_num)]
    exact EqFv 49 (by norm_num)
  · rw [gv_eq_T 689 (by norm_num)]
    exact DnFv 49 (by norm_num)

theorem bnd_690 : Gv 690 = 13488329183 ∧ LOG1E13LB ≤ gv 690 := by
  constructor
  · rw [Gv_eq_T 690 (by norm_num)]
    exact EqFv 50 (by norm_num)
  · rw [gv_eq_T 690 (by norm_num)]
    exact DnFv 50 (by norm_num)

theorem bnd_691 : Gv 691 = 13472159613 ∧ LOG1E13LB ≤ gv 691 := by
  constructor
  · rw [Gv_eq_T 691 (by norm_num)]
    exact EqFv 51 (by norm_num)
  · rw [gv_eq_T 691 (by norm_num)]
    exact DnFv 51 (by norm_num)

theorem bnd_692 : Gv 692 = 13455700715 ∧ LOG1E13LB ≤ gv 692 := by
  constructor
  · rw [Gv_eq_T 692 (by norm_num)]
    exact EqFv 52 (by norm_num)
  · rw [gv_eq_T 692 (by norm_num)]
    exact DnFv 52 (by norm_num)

theorem bnd_693 : Gv 693 = 13438944031 ∧ LOG1E13LB ≤ gv 693 := by
  constructor
  · rw [Gv_eq_T 693 (by norm_num)]
    exact EqFv 53 (by norm_num)
  · rw [gv_eq_T 693 (by norm_num)]
    exact DnFv 53 (by norm_num)

theorem bnd_694 : Gv 694 = 13421887293 ∧ LOG1E13LB ≤ gv 694 := by
  constructor
  · rw [Gv_eq_T 694 (by norm_num)]
    exact EqFv 54 (by norm_num)
  · rw [gv_eq_T 694 (by norm_num)]
    exact DnFv 54 (by norm_num)

theorem bnd_695 : Gv 695 = 13404520037 ∧ LOG1E13LB ≤ gv 695 := by
  constructor
  · rw [Gv_eq_T 695 (by norm_num)]
    exact EqFv 55 (by norm_num)
  · rw [gv_eq_T 695 (by norm_num)]
    exact DnFv 55 (by norm_num)

theorem bnd_696 : Gv 696 = 13386833653 ∧ LOG1E13LB ≤ gv 696 := by
  constructor
  · rw [Gv_eq_T 696 (by norm_num)]
    exact EqFv 56 (by norm_num)
  · rw [gv_eq_T 696 (by norm_num)]
    exact DnFv 56 (by norm_num)

theorem bnd_697 : Gv 697 = 13368827175 ∧ LOG1E13LB ≤ gv 697 := by
  constructor
  · rw [Gv_eq_T 697 (by norm_num)]
    exact EqFv 57 (by norm_num)
  · rw [gv_eq_T 697 (by norm_num)]
    exact DnFv 57 (by norm_num)

theorem bnd_698 : Gv 698 = 13350485409 ∧ LOG1E13LB ≤ gv 698 := by
  constructor
  · rw [Gv_eq_T 698 (by norm_num)]
    exact EqFv 58 (by norm_num)
  · rw [gv_eq_T 698 (by norm_num)]
    exact DnFv 58 (by norm_num)

theorem bnd_699 : Gv 699 = 13331802621 ∧ LOG1E13LB ≤ gv 699 := by
  constructor
  · rw [Gv_eq_T 699 (by norm_num)]
    exact EqFv 59 (by norm_num)
  · rw [gv_eq_T 699 (by norm_num)]
    exact DnFv 59 (by norm_num)

theorem bnd_700 : Gv 700 = 13312770091 ∧ LOG1E13LB ≤ gv 700 := by
  constructor
  · rw [Gv_eq_T 700 (by norm_num)]
    exact EqFv 60 (by norm_num)
  · rw [gv_eq_T 700 (by norm_num)]
    exact DnFv 60 (by norm_num)

theorem bnd_701 : Gv 701 = 13293383291 ∧ LOG1E13LB ≤ gv 701 := by
  constructor
  · rw [Gv_eq_T 701 (by norm_num)]
    exact EqFv 61 (by norm_num)
  · rw [gv_eq_T 701 (by norm_num)]
    exact DnFv 61 (by norm_num)

theorem bnd_702 : Gv 702 = 13273626761 ∧ LOG1E13LB ≤ gv 702 := by
  constructor
  · rw [Gv_eq_T 702 (by norm_num)]
    exact EqFv 62 (by norm_num)
  · rw [gv_eq_T 702 (by norm_num)]
    exact DnFv 62 (by norm_num)

theorem bnd_703 : Gv 703 = 13253484671 ∧ LOG1E13LB ≤ gv 703 := by
  constructor
  · rw [Gv_eq_T 703 (by norm_num)]
    exact EqFv 63 (by norm_num)
  · rw [gv_eq_T 703 (by norm_num)]
    exact DnFv 63 (by norm_num)

theorem bnd_704 : Gv 704 = 13232969837 ∧ LOG1E13LB ≤ gv 704 := by
  constructor
  · rw [Gv_eq_T 704 (by norm_num)]
    exact EqFv 64 (by norm_num)
  · rw [gv_eq_T 704 (by norm_num)]
    exact DnFv 64 (by norm_num)

theorem bnd_705 : Gv 705 = 13212045031 ∧ LOG1E13LB ≤ gv 705 := by
  constructor
  · rw [Gv_eq_T 705 (by norm_num)]
    exact EqFv 65 (by norm_num)
  · rw [gv_eq_T 705 (by norm_num)]
    exact DnFv 65 (by norm_num)

theorem bnd_706 : Gv 706 = 13190709147 ∧ LOG1E13LB ≤ gv 706 := by
  constructor
  · rw [Gv_eq_T 706 (by norm_num)]
    exact EqFv 66 (by norm_num)
  · rw [gv_eq_T 706 (by norm_num)]
    exact DnFv 66 (by norm_num)

theorem bnd_707 : Gv 707 = 13168965367 ∧ LOG1E13LB ≤ gv 707 := by
  constructor
  · rw [Gv_eq_T 707 (by norm_num)]
    exact EqFv 67 (by norm_num)
  · rw [gv_eq_T 707 (by norm_num)]
    exact DnFv 67 (by norm_num)

theorem bnd_708 : Gv 708 = 13146784915 ∧ LOG1E13LB ≤ gv 708 := by
  constructor
  · rw [Gv_eq_T 708 (by norm_num)]
    exact EqFv 68 (by norm_num)
  · rw [gv_eq_T 708 (by norm_num)]
    exact DnFv 68 (by norm_num)

theorem bnd_709 : Gv 709 = 13124161671 ∧ LOG1E13LB ≤ gv 709 := by
  constructor
  · rw [Gv_eq_T 709 (by norm_num)]
    exact EqFv 69 (by norm_num)
  · rw [gv_eq_T 709 (by norm_num)]
    exact DnFv 69 (by norm_num)

theorem bnd_710 : Gv 710 = 13101084183 ∧ LOG1E13LB ≤ gv 710 := by
  constructor
  · rw [Gv_eq_T 710 (by norm_num)]
    exact EqFv 70 (by norm_num)
  · rw [gv_eq_T 710 (by norm_num)]
    exact DnFv 70 (by norm_num)

theorem bnd_711 : Gv 711 = 13077536455 ∧ LOG1E13LB ≤ gv 711 := by
  constructor
  · rw [Gv_eq_T 711 (by norm_num)]
    exact EqFv 71 (by norm_num)
  · rw [gv_eq_T 711 (by norm_num)]
    exact DnFv 71 (by norm_num)

theorem bnd_712 : Gv 712 = 13053505787 ∧ LOG1E13LB ≤ gv 712 := by
  constructor
  · rw [Gv_eq_T 712 (by norm_num)]
    exact EqFv 72 (by norm_num)
  · rw [gv_eq_T 712 (by norm_num)]
    exact DnFv 72 (by norm_num)

theorem bnd_713 : Gv 713 = 13028981277 ∧ LOG1E13LB ≤ gv 713 := by
  constructor
  · rw [Gv_eq_T 713 (by norm_num)]
    exact EqFv 73 (by norm_num)
  · rw [gv_eq_T 713 (by norm_num)]
    exact DnFv 73 (by norm_num)

theorem bnd_714 : Gv 714 = 13003947411 ∧ LOG1E13LB ≤ gv 714 := by
  constructor
  · rw [Gv_eq_T 714 (by norm_num)]
    exact EqFv 74 (by norm_num)
  · rw [gv_eq_T 714 (by norm_num)]
    exact DnFv 74 (by norm_num)

theorem bnd_715 : Gv 715 = 12978383945 ∧ LOG1E13LB ≤ gv 715 := by
  constructor
  · rw [Gv_eq_T 715 (by norm_num)]
    exact EqFv 75 (by norm_num)
  · rw [gv_eq_T 715 (by norm_num)]
    exact DnFv 75 (by norm_num)

theorem bnd_716 : Gv 716 = 12952283289 ∧ LOG1E13LB ≤ gv 716 := by
  constructor
  · rw [Gv_eq_T 716 (by norm_num)]
    exact EqFv 76 (by norm_num)
  · rw [gv_eq_T 716 (by norm_num)]
    exact DnFv 76 (by norm_num)

theorem bnd_717 : Gv 717 = 12925621241 ∧ LOG1E13LB ≤ gv 717 := by
  constructor
  · rw [Gv_eq_T 717 (by norm_num)]
    exact EqFv 77 (by norm_num)
  · rw [gv_eq_T 717 (by norm_num)]
    exact DnFv 77 (by norm_num)

theorem bnd_718 : Gv 718 = 12898386195 ∧ LOG1E13LB ≤ gv 718 := by
  constructor
  · rw [Gv_eq_T 718 (by norm_num)]
    exact EqFv 78 (by norm_num)
  · rw [gv_eq_T 718 (by norm_num)]
    exact DnFv 78 (by norm_num)

theorem bnd_719 : Gv 719 = 12870560217 ∧ LOG1E13LB ≤ gv 719 := by
  constructor
  · rw [Gv_eq_T 719 (by norm_num)]
    exact EqFv 79 (by norm_num)
  · rw [gv_eq_T 719 (by norm_num)]
    exact DnFv 79 (by norm_num)

theorem bnd_720 : Gv 720 = 12842121661 ∧ LOG1E13LB ≤ gv 720 := by
  constructor
  · rw [Gv_eq_T 720 (by norm_num)]
    exact EqFv 80 (by norm_num)
  · rw [gv_eq_T 720 (by norm_num)]
    exact DnFv 80 (by norm_num)

theorem bnd_721 : Gv 721 = 12813043025 ∧ LOG1E13LB ≤ gv 721 := by
  constructor
  · rw [Gv_eq_T 721 (by norm_num)]
    exact EqFv 81 (by norm_num)
  · rw [gv_eq_T 721 (by norm_num)]
    exact DnFv 81 (by norm_num)

theorem bnd_722 : Gv 722 = 12783320971 ∧ LOG1E13LB ≤ gv 722 := by
  constructor
  · rw [Gv_eq_T 722 (by norm_num)]
    exact EqFv 82 (by norm_num)
  · rw [gv_eq_T 722 (by norm_num)]
    exact DnFv 82 (by norm_num)

theorem bnd_723 : Gv 723 = 12752923131 ∧ LOG1E13LB ≤ gv 723 := by
  constructor
  · rw [Gv_eq_T 723 (by norm_num)]
    exact EqFv 83 (by norm_num)
  · rw [gv_eq_T 723 (by norm_num)]
    exact DnFv 83 (by norm_num)

theorem bnd_724 : Gv 724 = 12721824573 ∧ LOG1E13LB ≤ gv 724 := by
  constructor
  · rw [Gv_eq_T 724 (by norm_num)]
    exact EqFv 84 (by norm_num)
  · rw [gv_eq_T 724 (by norm_num)]
    exact DnFv 84 (by norm_num)

theorem bnd_725 : Gv 725 = 12690010851 ∧ LOG1E13LB ≤ gv 725 := by
  constructor
  · rw [Gv_eq_T 725 (by norm_num)]
    exact EqFv 85 (by norm_num)
  · rw [gv_eq_T 725 (by norm_num)]
    exact DnFv 85 (by norm_num)

theorem bnd_726 : Gv 726 = 12657448237 ∧ LOG1E13LB ≤ gv 726 := by
  constructor
  · rw [Gv_eq_T 726 (by norm_num)]
    exact EqFv 86 (by norm_num)
  · rw [gv_eq_T 726 (by norm_num)]
    exact DnFv 86 (by norm_num)

theorem bnd_727 : Gv 727 = 12624115235 ∧ LOG1E13LB ≤ gv 727 := by
  constructor
  · rw [Gv_eq_T 727 (by norm_num)]
    exact EqFv 87 (by norm_num)
  · rw [gv_eq_T 727 (by norm_num)]
    exact DnFv 87 (by norm_num)

theorem bnd_728 : Gv 728 = 12589983693 ∧ LOG1E13LB ≤ gv 728 := by
  constructor
  · rw [Gv_eq_T 728 (by norm_num)]
    exact EqFv 88 (by norm_num)
  · rw [gv_eq_T 728 (by norm_num)]
    exact DnFv 88 (by norm_num)

theorem bnd_729 : Gv 729 = 12555031123 ∧ LOG1E13LB ≤ gv 729 := by
  constructor
  · rw [Gv_eq_T 729 (by norm_num)]
    exact EqFv 89 (by norm_num)
  · rw [gv_eq_T 729 (by norm_num)]
    exact DnFv 89 (by norm_num)

theorem bnd_730 : Gv 730 = 12519206741 ∧ LOG1E13LB ≤ gv 730 := by
  constructor
  · rw [Gv_eq_T 730 (by norm_num)]
    exact EqFv 90 (by norm_num)
  · rw [gv_eq_T 730 (by norm_num)]
    exact DnFv 90 (by norm_num)

theorem bnd_731 : Gv 731 = 12482500509 ∧ LOG1E13LB ≤ gv 731 := by
  constructor
  · rw [Gv_eq_T 731 (by norm_num)]
    exact EqFv 91 (by norm_num)
  · rw [gv_eq_T 731 (by norm_num)]
    exact DnFv 91 (by norm_num)

theorem bnd_732 : Gv 732 = 12444875843 ∧ LOG1E13LB ≤ gv 732 := by
  constructor
  · rw [Gv_eq_T 732 (by norm_num)]
    exact EqFv 92 (by norm_num)
  · rw [gv_eq_T 732 (by norm_num)]
    exact DnFv 92 (by norm_num)

theorem bnd_733 : Gv 733 = 12406283199 ∧ LOG1E13LB ≤ gv 733 := by
  constructor
  · rw [Gv_eq_T 733 (by norm_num)]
    exact EqFv 93 (by norm_num)
  · rw [gv_eq_T 733 (by norm_num)]
    exact DnFv 93 (by norm_num)

theorem bnd_734 : Gv 734 = 12366696905 ∧ LOG1E13LB ≤ gv 734 := by
  constructor
  · rw [Gv_eq_T 734 (by norm_num)]
    exact EqFv 94 (by norm_num)
  · rw [gv_eq_T 734 (by norm_num)]
    exact DnFv 94 (by norm_num)

theorem bnd_735 : Gv 735 = 12326079157 ∧ LOG1E13LB ≤ gv 735 := by
  constructor
  · rw [Gv_eq_T 735 (by norm_num)]
    exact EqFv 95 (by norm_num)
  · rw [gv_eq_T 735 (by norm_num)]
    exact DnFv 95 (by norm_num)

theorem bnd_736 : Gv 736 = 12284375921 ∧ LOG1E13LB ≤ gv 736 := by
  constructor
  · rw [Gv_eq_T 736 (by norm_num)]
    exact EqFv 96 (by norm_num)
  · rw [gv_eq_T 736 (by norm_num)]
    exact DnFv 96 (by norm_num)

theorem bnd_737 : Gv 737 = 12241550885 ∧ LOG1E13LB ≤ gv 737 := by
  constructor
  · rw [Gv_eq_T 737 (by norm_num)]
    exact EqFv 97 (by norm_num)
  · rw [gv_eq_T 737 (by norm_num)]
    exact DnFv 97 (by norm_num)

theorem bnd_738 : Gv 738 = 12197556239 ∧ LOG1E13LB ≤ gv 738 := by
  constructor
  · rw [Gv_eq_T 738 (by norm_num)]
    exact EqFv 98 (by norm_num)
  · rw [gv_eq_T 738 (by norm_num)]
    exact DnFv 98 (by norm_num)

theorem bnd_739 : Gv 739 = 12152334713 ∧ LOG1E13LB ≤ gv 739 := by
  constructor
  · rw [Gv_eq_T 739 (by norm_num)]
    exact EqFv 99 (by norm_num)
  · rw [gv_eq_T 739 (by norm_num)]
    exact DnFv 99 (by norm_num)

theorem bnd_740 : Gv 740 = 12105842807 ∧ LOG1E13LB ≤ gv 740 := by
  constructor
  · rw [Gv_eq_T 740 (by norm_num)]
    exact EqFv 100 (by norm_num)
  · rw [gv_eq_T 740 (by norm_num)]
    exact DnFv 100 (by norm_num)

theorem bnd_741 : Gv 741 = 12058018159 ∧ LOG1E13LB ≤ gv 741 := by
  constructor
  · rw [Gv_eq_T 741 (by norm_num)]
    exact EqFv 101 (by norm_num)
  · rw [gv_eq_T 741 (by norm_num)]
    exact DnFv 101 (by norm_num)

theorem bnd_742 : Gv 742 = 12008800663 ∧ LOG1E13LB ≤ gv 742 := by
  constructor
  · rw [Gv_eq_T 742 (by norm_num)]
    exact EqFv 102 (by norm_num)
  · rw [gv_eq_T 742 (by norm_num)]
    exact DnFv 102 (by norm_num)

theorem bnd_743 : Gv 743 = 11958123627 ∧ LOG1E13LB ≤ gv 743 := by
  constructor
  · rw [Gv_eq_T 743 (by norm_num)]
    exact EqFv 103 (by norm_num)
  · rw [gv_eq_T 743 (by norm_num)]
    exact DnFv 103 (by norm_num)

theorem bnd_744 : Gv 744 = 11905918413 ∧ LOG1E13LB ≤ gv 744 := by
  constructor
  · rw [Gv_eq_T 744 (by norm_num)]
    exact EqFv 104 (by norm_num)
  · rw [gv_eq_T 744 (by norm_num)]
    exact DnFv 104 (by norm_num)

theorem bnd_745 : Gv 745 = 11852111333 ∧ LOG1E13LB ≤ gv 745 := by
  constructor
  · rw [Gv_eq_T 745 (by norm_num)]
    exact EqFv 105 (by norm_num)
  · rw [gv_eq_T 745 (by norm_num)]
    exact DnFv 105 (by norm_num)

theorem bnd_746 : Gv 746 = 11796618537 ∧ LOG1E13LB ≤ gv 746 := by
  constructor
  · rw [Gv_eq_T 746 (by norm_num)]
    exact EqFv 106 (by norm_num)
  · rw [gv_eq_T 746 (by norm_num)]
    exact DnFv 106 (by norm_num)

theorem bnd_747 : Gv 747 = 11739357583 ∧ LOG1E13LB ≤ gv 747 := by
  constructor
  · rw [Gv_eq_T 747 (by norm_num)]
    exact EqFv 107 (by norm_num)
  · rw [gv_eq_T 747 (by norm_num)]
    exact DnFv 107 (by norm_num)

theorem bnd_748 : Gv 748 = 11680237743 ∧ LOG1E13LB ≤ gv 748 := by
  constructor
  · rw [Gv_eq_T 748 (by norm_num)]
    exact EqFv 108 (by norm_num)
  · rw [gv_eq_T 748 (by norm_num)]
    exact DnFv 108 (by norm_num)

theorem bnd_749 : Gv 749 = 11619152915 ∧ LOG1E13LB ≤ gv 749 := by
  constructor
  · rw [Gv_eq_T 749 (by norm_num)]
    exact EqFv 109 (by norm_num)
  · rw [gv_eq_T 749 (by norm_num)]
    exact DnFv 109 (by norm_num)

theorem bnd_750 : Gv 750 = 11555983995 ∧ LOG1E13LB ≤ gv 750 := by
  constructor
  · rw [Gv_eq_T 750 (by norm_num)]
    exact EqFv 110 (by norm_num)
  · rw [gv_eq_T 750 (by norm_num)]
    exact DnFv 110 (by norm_num)

theorem bnd_751 : Gv 751 = 11490636641 ∧ LOG1E13LB ≤ gv 751 := by
  constructor
  · rw [Gv_eq_T 751 (by norm_num)]
    exact EqFv 111 (by norm_num)
  · rw [gv_eq_T 751 (by norm_num)]
    exact DnFv 111 (by norm_num)

theorem bnd_752 : Gv 752 = 11422968821 ∧ LOG1E13LB ≤ gv 752 := by
  constructor
  · rw [Gv_eq_T 752 (by norm_num)]
    exact EqFv 112 (by norm_num)
  · rw [gv_eq_T 752 (by norm_num)]
    exact DnFv 112 (by norm_num)

theorem bnd_753 : Gv 753 = 11352828415 ∧ LOG1E13LB ≤ gv 753 := by
  constructor
  · rw [Gv_eq_T 753 (by norm_num)]
    exact EqFv 113 (by norm_num)
  · rw [gv_eq_T 753 (by norm_num)]
    exact DnFv 113 (by norm_num)

theorem bnd_754 : Gv 754 = 11280093096 ∧ LOG1E13LB ≤ gv 754 := by
  constructor
  · rw [Gv_eq_T 754 (by norm_num)]
    exact EqFv 114 (by norm_num)
  · rw [gv_eq_T 754 (by norm_num)]
    exact DnFv 114 (by norm_num)

theorem bnd_755 : Gv 755 = 11204574662 ∧ LOG1E13LB ≤ gv 755 := by
  constructor
  · rw [Gv_eq_T 755 (by norm_num)]
    exact EqFv 115 (by norm_num)
  · rw [gv_eq_T 755 (by norm_num)]
    exact DnFv 115 (by norm_num)

theorem bnd_756 : Gv 756 = 11126076496 ∧ LOG1E13LB ≤ gv 756 := by
  constructor
  · rw [Gv_eq_T 756 (by norm_num)]
    exact EqFv 116 (by norm_num)
  · rw [gv_eq_T 756 (by norm_num)]
    exact DnFv 116 (by norm_num)

theorem bnd_757 : Gv 757 = 11044414422 ∧ LOG1E13LB ≤ gv 757 := by
  constructor
  · rw [Gv_eq_T 757 (by norm_num)]
    exact EqFv 117 (by norm_num)
  · rw [gv_eq_T 757 (by norm_num)]
    exact DnFv 117 (by norm_num)

theorem bnd_758 : Gv 758 = 10959356422 ∧ LOG1E13LB ≤ gv 758 := by
  constructor
  · rw [Gv_eq_T 758 (by norm_num)]
    exact EqFv 118 (by norm_num)
  · rw [gv_eq_T 758 (by norm_num)]
    exact DnFv 118 (by norm_num)

theorem bnd_759 : Gv 759 = 10870656608 ∧ LOG1E13LB ≤ gv 759 := by
  constructor
  · rw [Gv_eq_T 759 (by norm_num)]
    exact EqFv 119 (by norm_num)
  · rw [gv_eq_T 759 (by norm_num)]
    exact DnFv 119 (by norm_num)

theorem bnd_760 : Gv 760 = 10778022308 ∧ LOG1E13LB ≤ gv 760 := by
  constructor
  · rw [Gv_eq_T 760 (by norm_num)]
    exact EqFv 120 (by norm_num)
  · rw [gv_eq_T 760 (by norm_num)]
    exact DnFv 120 (by norm_num)

theorem bnd_761 : Gv 761 = 10681163524 ∧ LOG1E13LB ≤ gv 761 := by
  constructor
  · rw [Gv_eq_T 761 (by norm_num)]
    exact EqFv 121 (by norm_num)
  · rw [gv_eq_T 761 (by norm_num)]
    exact DnFv 121 (by norm_num)

theorem bnd_762 : Gv 762 = 10579702348 ∧ LOG1E13LB ≤ gv 762 := by
  constructor
  · rw [Gv_eq_T 762 (by norm_num)]
    exact EqFv 122 (by norm_num)
  · rw [gv_eq_T 762 (by norm_num)]
    exact DnFv 122 (by norm_num)

theorem bnd_763 : Gv 763 = 10473254574 ∧ LOG1E13LB ≤ gv 763 := by
  constructor
  · rw [Gv_eq_T 763 (by norm_num)]
    exact EqFv 123 (by norm_num)
  · rw [gv_eq_T 763 (by norm_num)]
    exact DnFv 123 (by norm_num)

theorem bnd_764 : Gv 764 = 10361377824 ∧ LOG1E13LB ≤ gv 764 := by
  constructor
  · rw [Gv_eq_T 764 (by norm_num)]
    exact EqFv 124 (by norm_num)
  · rw [gv_eq_T 764 (by norm_num)]
    exact DnFv 124 (by norm_num)

theorem bnd_765 : Gv 765 = 10243541024 ∧ LOG1E13LB ≤ gv 765 := by
  constructor
  · rw [Gv_eq_T 765 (by norm_num)]
    exact EqFv 125 (by norm_num)
  · rw [gv_eq_T 765 (by norm_num)]
    exact DnFv 125 (by norm_num)

theorem bnd_766 : Gv 766 = 10119168214 ∧ LOG1E13LB ≤ gv 766 := by
  constructor
  · rw [Gv_eq_T 766 (by norm_num)]
    exact EqFv 126 (by norm_num)
  · rw [gv_eq_T 766 (by norm_num)]
    exact DnFv 126 (by norm_num)

theorem bnd_767 : Gv 767 = 9987597504 ∧ LOG1E13LB ≤ gv 767 := by
  constructor
  · rw [Gv_eq_T 767 (by norm_num)]
    exact EqFv 127 (by norm_num)
  · rw [gv_eq_T 767 (by norm_num)]
    exact DnFv 127 (by norm_num)

theorem bnd_768 : Gv 768 = 9847943974 ∧ LOG1E13LB ≤ gv 768 := by
  constructor
  · rw [Gv_eq_T 768 (by norm_num)]
    exact EqGv 0 (by norm_num)
  · rw [gv_eq_T 768 (by norm_num)]
    exact DnGv 0 (by norm_num)

theorem bnd_769 : Gv 769 = 9699633088 ∧ LOG1E13LB ≤ gv 769 := by
  constructor
  · rw [Gv_eq_T 769 (by norm_num)]
    exact EqGv 1 (by norm_num)
  · rw [gv_eq_T 769 (by norm_num)]
    exact DnGv 1 (by norm_num)

theorem bnd_770 : Gv 770 = 9541319846 ∧ LOG1E13LB ≤ gv 770 := by
  constructor
  · rw [Gv_eq_T 770 (by norm_num)]
    exact EqGv 2 (by norm_num)
  · rw [gv_eq_T 770 (by norm_num)]
    exact DnGv 2 (by norm_num)

theorem bnd_771 : Gv 771 = 9371996408 ∧ LOG1E13LB ≤ gv 771 := by
  constructor
  · rw [Gv_eq_T 771 (by norm_num)]
    exact EqGv 3 (by norm_num)
  · rw [gv_eq_T 771 (by norm_num)]
    exact DnGv 3 (by norm_num)

theorem bnd_772 : Gv 772 = 9190522350 ∧ LOG1E13LB ≤ gv 772 := by
  constructor
  · rw [Gv_eq_T 772 (by norm_num)]
    exact EqGv 4 (by norm_num)
  · rw [gv_eq_T 772 (by norm_num)]
    exact DnGv 4 (by norm_num)

theorem bnd_773 : Gv 773 = 8995895382 ∧ LOG1E13LB ≤ gv 773 := by
  constructor
  · rw [Gv_eq_T 773 (by norm_num)]
    exact EqGv 5 (by norm_num)
  · rw [gv_eq_T 773 (by norm_num)]
    exact DnGv 5 (by norm_num)

theorem bnd_774 : Gv 774 = 8787943576 ∧ LOG1E13LB ≤ gv 774 := by
  constructor
  · rw [Gv_eq_T 774 (by norm_num)]
    exact EqGv 6 (by norm_num)
  · rw [gv_eq_T 774 (by norm_num)]
    exact DnGv 6 (by norm_num)

theorem bnd_775 : Gv 775 = 8569583178 ∧ LOG1E13LB ≤ gv 775 := by
  constructor
  · rw [Gv_eq_T 775 (by norm_num)]
    exact EqGv 7 (by norm_num)
  · rw [gv_eq_T 775 (by norm_num)]
    exact DnGv 7 (by norm_num)

theorem bnd_776 : Gv 776 = 8354805550 ∧ LOG1E13LB ≤ gv 776 := by
  constructor
  · rw [Gv_eq_T 776 (by norm_num)]
    exact EqGv 8 (by norm_num)
  · rw [gv_eq_T 776 (by norm_num)]
    exact DnGv 8 (by norm_num)

theorem bnd_777 : Gv 777 = 8209862120 ∧ LOG1E13LB ≤ gv 777 := by
  constructor
  · rw [Gv_eq_T 777 (by norm_num)]
    exact EqGv 9 (by norm_num)
  · rw [gv_eq_T 777 (by norm_num)]
    exact DnGv 9 (by norm_num)

theorem bnd_778 : Gv 778 = 8701749672 ∧ LOG1E13LB ≤ gv 778 := by
  constructor
  · rw [Gv_eq_T 778 (by norm_num)]
    exact EqGv 10 (by norm_num)
  · rw [gv_eq_T 778 (by norm_num)]
    exact DnGv 10 (by norm_num)

theorem bnd_779 : Gv 779 = 8234819066 ∧ LOG1E13LB ≤ gv 779 := by
  constructor
  · rw [Gv_eq_T 779 (by norm_num)]
    exact EqGv 11 (by norm_num)
  · rw [gv_eq_T 779 (by norm_num)]
    exact DnGv 11 (by norm_num)

theorem bnd_780 : Gv 780 = 4790445386 ∧ LOG1E13LB ≤ gv 780 := by
  constructor
  · rw [Gv_eq_T 780 (by norm_num)]
    exact EqGv 12 (by norm_num)
  · rw [gv_eq_T 780 (by norm_num)]
    exact DnGv 12 (by norm_num)

theorem bnd_781 : Gv 781 = 3829667210 ∧ LOG1E13LB ≤ gv 781 := by
  constructor
  · rw [Gv_eq_T 781 (by norm_num)]
    exact EqGv 13 (by norm_num)
  · rw [gv_eq_T 781 (by norm_num)]
    exact DnGv 13 (by norm_num)

theorem bnd_782 : Gv 782 = 3294567522 ∧ LOG1E13LB ≤ gv 782 := by
  constructor
  · rw [Gv_eq_T 782 (by norm_num)]
    exact EqGv 14 (by norm_num)
  · rw [gv_eq_T 782 (by norm_num)]
    exact DnGv 14 (by norm_num)

theorem bnd_783 : Gv 783 = 2919481890 ∧ LOG1E13LB ≤ gv 783 := by
  constructor
  · rw [Gv_eq_T 783 (by norm_num)]
    exact EqGv 15 (by norm_num)
  · rw [gv_eq_T 783 (by norm_num)]
    exact DnGv 15 (by norm_num)

theorem bnd_784 : Gv 784 = 2639614446 ∧ LOG1E13LB ≤ gv 784 := by
  constructor
  · rw [Gv_eq_T 784 (by norm_num)]
    exact EqGv 16 (by norm_num)
  · rw [gv_eq_T 784 (by norm_num)]
    exact DnGv 16 (by norm_num)

theorem bnd_785 : Gv 785 = 2427384348 ∧ LOG1E13LB ≤ gv 785 := by
  constructor
  · rw [Gv_eq_T 785 (by norm_num)]
    exact EqGv 17 (by norm_num)
  · rw [gv_eq_T 785 (by norm_num)]
    exact DnGv 17 (by norm_num)

theorem bnd_786 : Gv 786 = 2266753176 ∧ LOG1E13LB ≤ gv 786 := by
  constructor
  · rw [Gv_eq_T 786 (by norm_num)]
    exact EqGv 18 (by norm_num)
  · rw [gv_eq_T 786 (by norm_num)]
    exact DnGv 18 (by norm_num)

theorem bnd_787 : Gv 787 = 2146163634 ∧ LOG1E13LB ≤ gv 787 := by
  constructor
  · rw [Gv_eq_T 787 (by norm_num)]
    exact EqGv 19 (by norm_num)
  · rw [gv_eq_T 787 (by norm_num)]
    exact DnGv 19 (by norm_num)

theorem bnd_788 : Gv 788 = 2056355776 ∧ LOG1E13LB ≤ gv 788 := by
  constructor
  · rw [Gv_eq_T 788 (by norm_num)]
    exact EqGv 20 (by norm_num)
  · rw [gv_eq_T 788 (by norm_num)]
    exact DnGv 20 (by norm_num)

theorem bnd_789 : Gv 789 = 1989290098 ∧ LOG1E13LB ≤ gv 789 := by
  constructor
  · rw [Gv_eq_T 789 (by norm_num)]
    exact EqGv 21 (by norm_num)
  · rw [gv_eq_T 789 (by norm_num)]
    exact DnGv 21 (by norm_num)

theorem bnd_790 : Gv 790 = 1938103570 ∧ LOG1E13LB ≤ gv 790 := by
  constructor
  · rw [Gv_eq_T 790 (by norm_num)]
    exact EqGv 22 (by norm_num)
  · rw [gv_eq_T 790 (by norm_num)]
    exact DnGv 22 (by norm_num)

theorem bnd_791 : Gv 791 = 1896644990 ∧ LOG1E13LB ≤ gv 791 := by
  constructor
  · rw [Gv_eq_T 791 (by norm_num)]
    exact EqGv 23 (by norm_num)
  · rw [gv_eq_T 791 (by norm_num)]
    exact DnGv 23 (by norm_num)

theorem bnd_792 : Gv 792 = 1859700118 ∧ LOG1E13LB ≤ gv 792 := by
  constructor
  · rw [Gv_eq_T 792 (by norm_num)]
    exact EqGv 24 (by norm_num)
  · rw [gv_eq_T 792 (by norm_num)]
    exact DnGv 24 (by norm_num)

theorem bnd_793 : Gv 793 = 1822769108 ∧ LOG1E13LB ≤ gv 793 := by
  constructor
  · rw [Gv_eq_T 793 (by norm_num)]
    exact EqGv 25 (by norm_num)
  · rw [gv_eq_T 793 (by norm_num)]
    exact DnGv 25 (by norm_num)

theorem bnd_794 : Gv 794 = 1782188772 ∧ LOG1E13LB ≤ gv 794 := by
  constructor
  · rw [Gv_eq_T 794 (by norm_num)]
    exact EqGv 26 (by norm_num)
  · rw [gv_eq_T 794 (by norm_num)]
    exact DnGv 26 (by norm_num)

theorem bnd_795 : Gv 795 = 1734916162 ∧ LOG1E13LB ≤ gv 795 := by
  constructor
  · rw [Gv_eq_T 795 (by norm_num)]
    exact EqGv 27 (by norm_num)
  · rw [gv_eq_T 795 (by norm_num)]
    exact DnGv 27 (by norm_num)

theorem bnd_796 : Gv 796 = 1678464778 ∧ LOG1E13LB ≤ gv 796 := by
  constructor
  · rw [Gv_eq_T 796 (by norm_num)]
    exact EqGv 28 (by norm_num)
  · rw [gv_eq_T 796 (by norm_num)]
    exact DnGv 28 (by norm_num)

theorem bnd_797 : Gv 797 = 1611081684 ∧ LOG1E13LB ≤ gv 797 := by
  constructor
  · rw [Gv_eq_T 797 (by norm_num)]
    exact EqGv 29 (by norm_num)
  · rw [gv_eq_T 797 (by norm_num)]
    exact DnGv 29 (by norm_num)

theorem bnd_798 : Gv 798 = 1531474636 ∧ LOG1E13LB ≤ gv 798 := by
  constructor
  · rw [Gv_eq_T 798 (by norm_num)]
    exact EqGv 30 (by norm_num)
  · rw [gv_eq_T 798 (by norm_num)]
    exact DnGv 30 (by norm_num)

theorem bnd_799 : Gv 799 = 1438731690 ∧ LOG1E13LB ≤ gv 799 := by
  constructor
  · rw [Gv_eq_T 799 (by norm_num)]
    exact EqGv 31 (by norm_num)
  · rw [gv_eq_T 799 (by norm_num)]
    exact DnGv 31 (by norm_num)

theorem bnd_800 : Gv 800 = 1332412522 ∧ LOG1E13LB ≤ gv 800 := by
  constructor
  · rw [Gv_eq_T 800 (by norm_num)]
    exact EqGv 32 (by norm_num)
  · rw [gv_eq_T 800 (by norm_num)]
    exact DnGv 32 (by norm_num)

theorem bnd_801 : Gv 801 = 1212495704 ∧ LOG1E13LB ≤ gv 801 := by
  constructor
  · rw [Gv_eq_T 801 (by norm_num)]
    exact EqGv 33 (by norm_num)
  · rw [gv_eq_T 801 (by norm_num)]
    exact DnGv 33 (by norm_num)

theorem bnd_802 : Gv 802 = 1079154762 ∧ LOG1E13LB ≤ gv 802 := by
  constructor
  · rw [Gv_eq_T 802 (by norm_num)]
    exact EqGv 34 (by norm_num)
  · rw [gv_eq_T 802 (by norm_num)]
    exact DnGv 34 (by norm_num)

theorem bnd_803 : Gv 803 = 932909676 ∧ LOG1E13LB ≤ gv 803 := by
  constructor
  · rw [Gv_eq_T 803 (by norm_num)]
    exact EqGv 35 (by norm_num)
  · rw [gv_eq_T 803 (by norm_num)]
    exact DnGv 35 (by norm_num)

theorem bnd_804 : Gv 804 = 774436184 ∧ LOG1E13LB ≤ gv 804 := by
  constructor
  · rw [Gv_eq_T 804 (by norm_num)]
    exact EqGv 36 (by norm_num)
  · rw [gv_eq_T 804 (by norm_num)]
    exact DnGv 36 (by norm_num)

theorem bnd_805 : Gv 805 = 604641730 ∧ LOG1E13LB ≤ gv 805 := by
  constructor
  · rw [Gv_eq_T 805 (by norm_num)]
    exact EqGv 37 (by norm_num)
  · rw [gv_eq_T 805 (by norm_num)]
    exact DnGv 37 (by norm_num)

theorem bnd_806 : Gv 806 = 424496774 ∧ LOG1E13LB ≤ gv 806 := by
  constructor
  · rw [Gv_eq_T 806 (by norm_num)]
    exact EqGv 38 (by norm_num)
  · rw [gv_eq_T 806 (by norm_num)]
    exact DnGv 38 (by norm_num)

theorem bnd_807 : Gv 807 = 235177046 ∧ LOG1E13LB ≤ gv 807 := by
  constructor
  · rw [Gv_eq_T 807 (by norm_num)]
    exact EqGv 39 (by norm_num)
  · rw [gv_eq_T 807 (by norm_num)]
    exact DnGv 39 (by norm_num)

theorem bnd_808 : Gv 808 = 37902354 ∧ LOG1E13LB ≤ gv 808 := by
  constructor
  · rw [Gv_eq_T 808 (by norm_num)]
    exact EqGv 40 (by norm_num)
  · rw [gv_eq_T 808 (by norm_num)]
    exact DnGv 40 (by norm_num)

theorem bnd_809 : Gv 809 = -166057524 ∧ LOG1E13LB ≤ gv 809 := by
  constructor
  · rw [Gv_eq_T 809 (by norm_num)]
    exact EqGv 41 (by norm_num)
  · rw [gv_eq_T 809 (by norm_num)]
    exact DnGv 41 (by norm_num)

theorem bnd_810 : Gv 810 = -375340602 ∧ LOG1E13LB ≤ gv 810 := by
  constructor
  · rw [Gv_eq_T 810 (by norm_num)]
    exact EqGv 42 (by norm_num)
  · rw [gv_eq_T 810 (by norm_num)]
    exact DnGv 42 (by norm_num)

theorem bnd_811 : Gv 811 = -588463110 ∧ LOG1E13LB ≤ gv 811 := by
  constructor
  · rw [Gv_eq_T 811 (by norm_num)]
    exact EqGv 43 (by norm_num)
  · rw [gv_eq_T 811 (by norm_num)]
    exact DnGv 43 (by norm_num)

theorem bnd_812 : Gv 812 = -803932538 ∧ LOG1E13LB ≤ gv 812 := by
  constructor
  · rw [Gv_eq_T 812 (by norm_num)]
    exact EqGv 44 (by norm_num)
  · rw [gv_eq_T 812 (by norm_num)]
    exact DnGv 44 (by norm_num)

theorem bnd_813 : Gv 813 = -1020209896 ∧ LOG1E13LB ≤ gv 813 := by
  constructor
  · rw [Gv_eq_T 813 (by norm_num)]
    exact EqGv 45 (by norm_num)
  · rw [gv_eq_T 813 (by norm_num)]
    exact DnGv 45 (by norm_num)

theorem bnd_814 : Gv 814 = -1235654704 ∧ LOG1E13LB ≤ gv 814 := by
  constructor
  · rw [Gv_eq_T 814 (by norm_num)]
    exact EqGv 46 (by norm_num)
  · rw [gv_eq_T 814 (by norm_num)]
    exact DnGv 46 (by norm_num)

theorem bnd_815 : Gv 815 = -1448551110 ∧ LOG1E13LB ≤ gv 815 := by
  constructor
  · rw [Gv_eq_T 815 (by norm_num)]
    exact EqGv 47 (by norm_num)
  · rw [gv_eq_T 815 (by norm_num)]
    exact DnGv 47 (by norm_num)

theorem bnd_816 : Gv 816 = -1657150034 ∧ LOG1E13LB ≤ gv 816 := by
  constructor
  · rw [Gv_eq_T 816 (by norm_num)]
    exact EqGv 48 (by norm_num)
  · rw [gv_eq_T 816 (by norm_num)]
    exact DnGv 48 (by norm_num)

theorem bnd_817 : Gv 817 = -1859679926 ∧ LOG1E13LB ≤ gv 817 := by
  constructor
  · rw [Gv_eq_T 817 (by norm_num)]
    exact EqGv 49 (by norm_num)
  · rw [gv_eq_T 817 (by norm_num)]
    exact DnGv 49 (by norm_num)

theorem bnd_818 : Gv 818 = -2054294002 ∧ LOG1E13LB ≤ gv 818 := by
  constructor
  · rw [Gv_eq_T 818 (by norm_num)]
    exact EqGv 50 (by norm_num)
  · rw [gv_eq_T 818 (by norm_num)]
    exact DnGv 50 (by norm_num)

theorem bnd_819 : Gv 819 = -2239183782 ∧ LOG1E13LB ≤ gv 819 := by
  constructor
  · rw [Gv_eq_T 819 (by norm_num)]
    exact EqGv 51 (by norm_num)
  · rw [gv_eq_T 819 (by norm_num)]
    exact DnGv 51 (by norm_num)

theorem bnd_820 : Gv 820 = -2412540942 ∧ LOG1E13LB ≤ gv 820 := by
  constructor
  · rw [Gv_eq_T 820 (by norm_num)]
    exact EqGv 52 (by norm_num)
  · rw [gv_eq_T 820 (by norm_num)]
    exact DnGv 52 (by norm_num)

theorem bnd_821 : Gv 821 = -2572586902 ∧ LOG1E13LB ≤ gv 821 := by
  constructor
  · rw [Gv_eq_T 821 (by norm_num)]
    exact EqGv 53 (by norm_num)
  · rw [gv_eq_T 821 (by norm_num)]
    exact DnGv 53 (by norm_num)

theorem bnd_822 : Gv 822 = -2717754310 ∧ LOG1E13LB ≤ gv 822 := by
  constructor
  · rw [Gv_eq_T 822 (by norm_num)]
    exact EqGv 54 (by norm_num)
  · rw [gv_eq_T 822 (by norm_num)]
    exact DnGv 54 (by norm_num)

theorem bnd_823 : Gv 823 = -2846473398 ∧ LOG1E13LB ≤ gv 823 := by
  constructor
  · rw [Gv_eq_T 823 (by norm_num)]
    exact EqGv 55 (by norm_num)
  · rw [gv_eq_T 823 (by norm_num)]
    exact DnGv 55 (by norm_num)

theorem bnd_824 : Gv 824 = -2957440382 ∧ LOG1E13LB ≤ gv 824 := by
  constructor
  · rw [Gv_eq_T 824 (by norm_num)]
    exact EqGv 56 (by norm_num)
  · rw [gv_eq_T 824 (by norm_num)]
    exact DnGv 56 (by norm_num)

theorem bnd_825 : Gv 825 = -3049536678 ∧ LOG1E13LB ≤ gv 825 := by
  constructor
  · rw [Gv_eq_T 825 (by norm_num)]
    exact EqGv 57 (by norm_num)
  · rw [gv_eq_T 825 (by norm_num)]
    exact DnGv 57 (by norm_num)

theorem bnd_826 : Gv 826 = -3121795266 ∧ LOG1E13LB ≤ gv 826 := by
  constructor
  · rw [Gv_eq_T 826 (by norm_num)]
    exact EqGv 58 (by norm_num)
  · rw [gv_eq_T 826 (by norm_num)]
    exact DnGv 58 (by norm_num)

theorem bnd_827 : Gv 827 = -3173626530 ∧ LOG1E13LB ≤ gv 827 := by
  constructor
  · rw [Gv_eq_T 827 (by norm_num)]
    exact EqGv 59 (by norm_num)
  · rw [gv_eq_T 827 (by norm_num)]
    exact DnGv 59 (by norm_num)

theorem bnd_828 : Gv 828 = -3204613014 ∧ LOG1E13LB ≤ gv 828 := by
  constructor
  · rw [Gv_eq_T 828 (by norm_num)]
    exact EqGv 60 (by norm_num)
  · rw [gv_eq_T 828 (by norm_num)]
    exact DnGv 60 (by norm_num)

theorem bnd_829 : Gv 829 = -3203649688 ∧ LOG1E13LB ≤ gv 829 := by
  constructor
  · rw [Gv_eq_T 829 (by norm_num)]
    exact EqGv 61 (by norm_num)
  · rw [gv_eq_T 829 (by norm_num)]
    exact DnGv 61 (by norm_num)

theorem bnd_830 : Gv 830 = -3172692504 ∧ LOG1E13LB ≤ gv 830 := by
  constructor
  · rw [Gv_eq_T 830 (by norm_num)]
    exact EqGv 62 (by norm_num)
  · rw [gv_eq_T 830 (by norm_num)]
    exact DnGv 62 (by norm_num)

theorem bnd_831 : Gv 831 = -3122093162 ∧ LOG1E13LB ≤ gv 831 := by
  constructor
  · rw [Gv_eq_T 831 (by norm_num)]
    exact EqGv 63 (by norm_num)
  · rw [gv_eq_T 831 (by norm_num)]
    exact DnGv 63 (by norm_num)

theorem bnd_832 : Gv 832 = -3052790994 ∧ LOG1E13LB ≤ gv 832 := by
  constructor
  · rw [Gv_eq_T 832 (by norm_num)]
    exact EqGv 64 (by norm_num)
  · rw [gv_eq_T 832 (by norm_num)]
    exact DnGv 64 (by norm_num)

theorem bnd_833 : Gv 833 = -2965825956 ∧ LOG1E13LB ≤ gv 833 := by
  constructor
  · rw [Gv_eq_T 833 (by norm_num)]
    exact EqGv 65 (by norm_num)
  · rw [gv_eq_T 833 (by norm_num)]
    exact DnGv 65 (by norm_num)

theorem bnd_834 : Gv 834 = -2862448316 ∧ LOG1E13LB ≤ gv 834 := by
  constructor
  · rw [Gv_eq_T 834 (by norm_num)]
    exact EqGv 66 (by norm_num)
  · rw [gv_eq_T 834 (by norm_num)]
    exact DnGv 66 (by norm_num)

theorem bnd_835 : Gv 835 = -2744021018 ∧ LOG1E13LB ≤ gv 835 := by
  constructor
  · rw [Gv_eq_T 835 (by norm_num)]
    exact EqGv 67 (by norm_num)
  · rw [gv_eq_T 835 (by norm_num)]
    exact DnGv 67 (by norm_num)

theorem bnd_836 : Gv 836 = -2611972580 ∧ LOG1E13LB ≤ gv 836 := by
  constructor
  · rw [Gv_eq_T 836 (by norm_num)]
    exact EqGv 68 (by norm_num)
  · rw [gv_eq_T 836 (by norm_num)]
    exact DnGv 68 (by norm_num)

theorem bnd_837 : Gv 837 = -2467809874 ∧ LOG1E13LB ≤ gv 837 := by
  constructor
  · rw [Gv_eq_T 837 (by norm_num)]
    exact EqGv 69 (by norm_num)
  · rw [gv_eq_T 837 (by norm_num)]
    exact DnGv 69 (by norm_num)

theorem bnd_838 : Gv 838 = -2312950726 ∧ LOG1E13LB ≤ gv 838 := by
  constructor
  · rw [Gv_eq_T 838 (by norm_num)]
    exact EqGv 70 (by norm_num)
  · rw [gv_eq_T 838 (by norm_num)]
    exact DnGv 70 (by norm_num)

theorem bnd_839 : Gv 839 = -2148918840 ∧ LOG1E13LB ≤ gv 839 := by
  constructor
  · rw [Gv_eq_T 839 (by norm_num)]
    exact EqGv 71 (by norm_num)
  · rw [gv_eq_T 839 (by norm_num)]
    exact DnGv 71 (by norm_num)

theorem bnd_840 : Gv 840 = -1977102178 ∧ LOG1E13LB ≤ gv 840 := by
  constructor
  · rw [Gv_eq_T 840 (by norm_num)]
    exact EqGv 72 (by norm_num)
  · rw [gv_eq_T 840 (by norm_num)]
    exact DnGv 72 (by norm_num)

theorem bnd_841 : Gv 841 = -1798895800 ∧ LOG1E13LB ≤ gv 841 := by
  constructor
  · rw [Gv_eq_T 841 (by norm_num)]
    exact EqGv 73 (by norm_num)
  · rw [gv_eq_T 841 (by norm_num)]
    exact DnGv 73 (by norm_num)

theorem bnd_842 : Gv 842 = -1615511340 ∧ LOG1E13LB ≤ gv 842 := by
  constructor
  · rw [Gv_eq_T 842 (by norm_num)]
    exact EqGv 74 (by norm_num)
  · rw [gv_eq_T 842 (by norm_num)]
    exact DnGv 74 (by norm_num)

theorem bnd_843 : Gv 843 = -1428152136 ∧ LOG1E13LB ≤ gv 843 := by
  constructor
  · rw [Gv_eq_T 843 (by norm_num)]
    exact EqGv 75 (by norm_num)
  · rw [gv_eq_T 843 (by norm_num)]
    exact DnGv 75 (by norm_num)

theorem bnd_844 : Gv 844 = -1237832732 ∧ LOG1E13LB ≤ gv 844 := by
  constructor
  · rw [Gv_eq_T 844 (by norm_num)]
    exact EqGv 76 (by norm_num)
  · rw [gv_eq_T 844 (by norm_num)]
    exact DnGv 76 (by norm_num)

theorem bnd_845 : Gv 845 = -1045500742 ∧ LOG1E13LB ≤ gv 845 := by
  constructor
  · rw [Gv_eq_T 845 (by norm_num)]
    exact EqGv 77 (by norm_num)
  · rw [gv_eq_T 845 (by norm_num)]
    exact DnGv 77 (by norm_num)

theorem bnd_846 : Gv 846 = -851936390 ∧ LOG1E13LB ≤ gv 846 := by
  constructor
  · rw [Gv_eq_T 846 (by norm_num)]
    exact EqGv 78 (by norm_num)
  · rw [gv_eq_T 846 (by norm_num)]
    exact DnGv 78 (by norm_num)

theorem bnd_847 : Gv 847 = -657895450 ∧ LOG1E13LB ≤ gv 847 := by
  constructor
  · rw [Gv_eq_T 847 (by norm_num)]
    exact EqGv 79 (by norm_num)
  · rw [gv_eq_T 847 (by norm_num)]
    exact DnGv 79 (by norm_num)

theorem bnd_848 : Gv 848 = -463893772 ∧ LOG1E13LB ≤ gv 848 := by
  constructor
  · rw [Gv_eq_T 848 (by norm_num)]
    exact EqGv 80 (by norm_num)
  · rw [gv_eq_T 848 (by norm_num)]
    exact DnGv 80 (by norm_num)

theorem bnd_849 : Gv 849 = -270402892 ∧ LOG1E13LB ≤ gv 849 := by
  constructor
  · rw [Gv_eq_T 849 (by norm_num)]
    exact EqGv 81 (by norm_num)
  · rw [gv_eq_T 849 (by norm_num)]
    exact DnGv 81 (by norm_num)

theorem bnd_850 : Gv 850 = -77804814 ∧ LOG1E13LB ≤ gv 850 := by
  constructor
  · rw [Gv_eq_T 850 (by norm_num)]
    exact EqGv 82 (by norm_num)
  · rw [gv_eq_T 850 (by norm_num)]
    exact DnGv 82 (by norm_num)

theorem bnd_851 : Gv 851 = 113692852 ∧ LOG1E13LB ≤ gv 851 := by
  constructor
  · rw [Gv_eq_T 851 (by norm_num)]
    exact EqGv 83 (by norm_num)
  · rw [gv_eq_T 851 (by norm_num)]
    exact DnGv 83 (by norm_num)

theorem bnd_852 : Gv 852 = 303870500 ∧ LOG1E13LB ≤ gv 852 := by
  constructor
  · rw [Gv_eq_T 852 (by norm_num)]
    exact EqGv 84 (by norm_num)
  · rw [gv_eq_T 852 (by norm_num)]
    exact DnGv 84 (by norm_num)

theorem bnd_853 : Gv 853 = 492627622 ∧ LOG1E13LB ≤ gv 853 := by
  constructor
  · rw [Gv_eq_T 853 (by norm_num)]
    exact EqGv 85 (by norm_num)
  · rw [gv_eq_T 853 (by norm_num)]
    exact DnGv 85 (by norm_num)

theorem bnd_854 : Gv 854 = 679964138 ∧ LOG1E13LB ≤ gv 854 := by
  constructor
  · rw [Gv_eq_T 854 (by norm_num)]
    exact EqGv 86 (by norm_num)
  · rw [gv_eq_T 854 (by norm_num)]
    exact DnGv 86 (by norm_num)

theorem bnd_855 : Gv 855 = 865893730 ∧ LOG1E13LB ≤ gv 855 := by
  constructor
  · rw [Gv_eq_T 855 (by norm_num)]
    exact EqGv 87 (by norm_num)
  · rw [gv_eq_T 855 (by norm_num)]
    exact DnGv 87 (by norm_num)

theorem bnd_856 : Gv 856 = 1050437194 ∧ LOG1E13LB ≤ gv 856 := by
  constructor
  · rw [Gv_eq_T 856 (by norm_num)]
    exact EqGv 88 (by norm_num)
  · rw [gv_eq_T 856 (by norm_num)]
    exact DnGv 88 (by norm_num)

theorem bnd_857 : Gv 857 = 1233675084 ∧ LOG1E13LB ≤ gv 857 := by
  constructor
  · rw [Gv_eq_T 857 (by norm_num)]
    exact EqGv 89 (by norm_num)
  · rw [gv_eq_T 857 (by norm_num)]
    exact DnGv 89 (by norm_num)

theorem bnd_858 : Gv 858 = 1415727468 ∧ LOG1E13LB ≤ gv 858 := by
  constructor
  · rw [Gv_eq_T 858 (by norm_num)]
    exact EqGv 90 (by norm_num)
  · rw [gv_eq_T 858 (by norm_num)]
    exact DnGv 90 (by norm_num)

theorem bnd_859 : Gv 859 = 1596683376 ∧ LOG1E13LB ≤ gv 859 := by
  constructor
  · rw [Gv_eq_T 859 (by norm_num)]
    exact EqGv 91 (by norm_num)
  · rw [gv_eq_T 859 (by norm_num)]
    exact DnGv 91 (by norm_num)

theorem bnd_860 : Gv 860 = 1776602296 ∧ LOG1E13LB ≤ gv 860 := by
  constructor
  · rw [Gv_eq_T 860 (by norm_num)]
    exact EqGv 92 (by norm_num)
  · rw [gv_eq_T 860 (by norm_num)]
    exact DnGv 92 (by norm_num)

theorem bnd_861 : Gv 861 = 1955568846 ∧ LOG1E13LB ≤ gv 861 := by
  constructor
  · rw [Gv_eq_T 861 (by norm_num)]
    exact EqGv 93 (by norm_num)
  · rw [gv_eq_T 861 (by norm_num)]
    exact DnGv 93 (by norm_num)

theorem bnd_862 : Gv 862 = 2133612814 ∧ LOG1E13LB ≤ gv 862 := by
  constructor
  · rw [Gv_eq_T 862 (by norm_num)]
    exact EqGv 94 (by norm_num)
  · rw [gv_eq_T 862 (by norm_num)]
    exact DnGv 94 (by norm_num)

theorem bnd_863 : Gv 863 = 2310714366 ∧ LOG1E13LB ≤ gv 863 := by
  constructor
  · rw [Gv_eq_T 863 (by norm_num)]
    exact EqGv 95 (by norm_num)
  · rw [gv_eq_T 863 (by norm_num)]
    exact DnGv 95 (by norm_num)

theorem bnd_864 : Gv 864 = 2486814334 ∧ LOG1E13LB ≤ gv 864 := by
  constructor
  · rw [Gv_eq_T 864 (by norm_num)]
    exact EqGv 96 (by norm_num)
  · rw [gv_eq_T 864 (by norm_num)]
    exact DnGv 96 (by norm_num)

theorem bnd_865 : Gv 865 = 2661795390 ∧ LOG1E13LB ≤ gv 865 := by
  constructor
  · rw [Gv_eq_T 865 (by norm_num)]
    exact EqGv 97 (by norm_num)
  · rw [gv_eq_T 865 (by norm_num)]
    exact DnGv 97 (by norm_num)

theorem bnd_866 : Gv 866 = 2835459938 ∧ LOG1E13LB ≤ gv 866 := by
  constructor
  · rw [Gv_eq_T 866 (by norm_num)]
    exact EqGv 98 (by norm_num)
  · rw [gv_eq_T 866 (by norm_num)]
    exact DnGv 98 (by norm_num)

theorem bnd_867 : Gv 867 = 3007599376 ∧ LOG1E13LB ≤ gv 867 := by
  constructor
  · rw [Gv_eq_T 867 (by norm_num)]
    exact EqGv 99 (by norm_num)
  · rw [gv_eq_T 867 (by norm_num)]
    exact DnGv 99 (by norm_num)

theorem bnd_868 : Gv 868 = 3177834382 ∧ LOG1E13LB ≤ gv 868 := by
  constructor
  · rw [Gv_eq_T 868 (by norm_num)]
    exact EqGv 100 (by norm_num)
  · rw [gv_eq_T 868 (by norm_num)]
    exact DnGv 100 (by norm_num)

theorem bnd_869 : Gv 869 = 3345849992 ∧ LOG1E13LB ≤ gv 869 := by
  constructor
  · rw [Gv_eq_T 869 (by norm_num)]
    exact EqGv 101 (by norm_num)
  · rw [gv_eq_T 869 (by norm_num)]
    exact DnGv 101 (by norm_num)

theorem bnd_870 : Gv 870 = 3511098482 ∧ LOG1E13LB ≤ gv 870 := by
  constructor
  · rw [Gv_eq_T 870 (by norm_num)]
    exact EqGv 102 (by norm_num)
  · rw [gv_eq_T 870 (by norm_num)]
    exact DnGv 102 (by norm_num)

theorem bnd_871 : Gv 871 = 3673111094 ∧ LOG1E13LB ≤ gv 871 := by
  constructor
  · rw [Gv_eq_T 871 (by norm_num)]
    exact EqGv 103 (by norm_num)
  · rw [gv_eq_T 871 (by norm_num)]
    exact DnGv 103 (by norm_num)

theorem bnd_872 : Gv 872 = 3831244334 ∧ LOG1E13LB ≤ gv 872 := by
  constructor
  · rw [Gv_eq_T 872 (by norm_num)]
    exact EqGv 104 (by norm_num)
  · rw [gv_eq_T 872 (by norm_num)]
    exact DnGv 104 (by norm_num)

theorem bnd_873 : Gv 873 = 3984868144 ∧ LOG1E13LB ≤ gv 873 := by
  constructor
  · rw [Gv_eq_T 873 (by norm_num)]
    exact EqGv 105 (by norm_num)
  · rw [gv_eq_T 873 (by norm_num)]
    exact DnGv 105 (by norm_num)

theorem bnd_874 : Gv 874 = 4133234022 ∧ LOG1E13LB ≤ gv 874 := by
  constructor
  · rw [Gv_eq_T 874 (by norm_num)]
    exact EqGv 106 (by norm_num)
  · rw [gv_eq_T 874 (by norm_num)]
    exact DnGv 106 (by norm_num)

theorem bnd_875 : Gv 875 = 4275624070 ∧ LOG1E13LB ≤ gv 875 := by
  constructor
  · rw [Gv_eq_T 875 (by norm_num)]
    exact EqGv 107 (by norm_num)
  · rw [gv_eq_T 875 (by norm_num)]
    exact DnGv 107 (by norm_num)

theorem bnd_876 : Gv 876 = 4411243792 ∧ LOG1E13LB ≤ gv 876 := by
  constructor
  · rw [Gv_eq_T 876 (by norm_num)]
    exact EqGv 108 (by norm_num)
  · rw [gv_eq_T 876 (by norm_num)]
    exact DnGv 108 (by norm_num)

theorem bnd_877 : Gv 877 = 4539278738 ∧ LOG1E13LB ≤ gv 877 := by
  constructor
  · rw [Gv_eq_T 877 (by norm_num)]
    exact EqGv 109 (by norm_num)
  · rw [gv_eq_T 877 (by norm_num)]
    exact DnGv 109 (by norm_num)

theorem bnd_878 : Gv 878 = 4658935520 ∧ LOG1E13LB ≤ gv 878 := by
  constructor
  · rw [Gv_eq_T 878 (by norm_num)]
    exact EqGv 110 (by norm_num)
  · rw [gv_eq_T 878 (by norm_num)]
    exact DnGv 110 (by norm_num)

theorem bnd_879 : Gv 879 = 4769401616 ∧ LOG1E13LB ≤ gv 879 := by
  constructor
  · rw [Gv_eq_T 879 (by norm_num)]
    exact EqGv 111 (by norm_num)
  · rw [gv_eq_T 879 (by norm_num)]
    exact DnGv 111 (by norm_num)

theorem bnd_880 : Gv 880 = 4869925784 ∧ LOG1E13LB ≤ gv 880 := by
  constructor
  · rw [Gv_eq_T 880 (by norm_num)]
    exact EqGv 112 (by norm_num)
  · rw [gv_eq_T 880 (by norm_num)]
    exact DnGv 112 (by norm_num)

theorem bnd_881 : Gv 881 = 4959744620 ∧ LOG1E13LB ≤ gv 881 := by
  constructor
  · rw [Gv_eq_T 881 (by norm_num)]
    exact EqGv 113 (by norm_num)
  · rw [gv_eq_T 881 (by norm_num)]
    exact DnGv 113 (by norm_num)

theorem bnd_882 : Gv 882 = 5038202096 ∧ LOG1E13LB ≤ gv 882 := by
  constructor
  · rw [Gv_eq_T 882 (by norm_num)]
    exact EqGv 114 (by norm_num)
  · rw [gv_eq_T 882 (by norm_num)]
    exact DnGv 114 (by norm_num)

theorem bnd_883 : Gv 883 = 5104712072 ∧ LOG1E13LB ≤ gv 883 := by
  constructor
  · rw [Gv_eq_T 883 (by norm_num)]
    exact EqGv 115 (by norm_num)
  · rw [gv_eq_T 883 (by norm_num)]
    exact DnGv 115 (by norm_num)

theorem bnd_884 : Gv 884 = 5158766670 ∧ LOG1E13LB ≤ gv 884 := by
  constructor
  · rw [Gv_eq_T 884 (by norm_num)]
    exact EqGv 116 (by norm_num)
  · rw [gv_eq_T 884 (by norm_num)]
    exact DnGv 116 (by norm_num)

theorem bnd_885 : Gv 885 = 5199899940 ∧ LOG1E13LB ≤ gv 885 := by
  constructor
  · rw [Gv_eq_T 885 (by norm_num)]
    exact EqGv 117 (by norm_num)
  · rw [gv_eq_T 885 (by norm_num)]
    exact DnGv 117 (by norm_num)

theorem bnd_886 : Gv 886 = 5227875338 ∧ LOG1E13LB ≤ gv 886 := by
  constructor
  · rw [Gv_eq_T 886 (by norm_num)]
    exact EqGv 118 (by norm_num)
  · rw [gv_eq_T 886 (by norm_num)]
    exact DnGv 118 (by norm_num)

theorem bnd_887 : Gv 887 = 5242473654 ∧ LOG1E13LB ≤ gv 887 := by
  constructor
  · rw [Gv_eq_T 887 (by norm_num)]
    exact EqGv 119 (by norm_num)
  · rw [gv_eq_T 887 (by norm_num)]
    exact DnGv 119 (by norm_num)

theorem bnd_888 : Gv 888 = 5243610080 ∧ LOG1E13LB ≤ gv 888 := by
  constructor
  · rw [Gv_eq_T 888 (by norm_num)]
    exact EqGv 120 (by norm_num)
  · rw [gv_eq_T 888 (by norm_num)]
    exact DnGv 120 (by norm_num)

theorem bnd_889 : Gv 889 = 5243524880 ∧ LOG1E13LB ≤ gv 889 := by
  constructor
  · rw [Gv_eq_T 889 (by norm_num)]
    exact EqGv 121 (by norm_num)
  · rw [gv_eq_T 889 (by norm_num)]
    exact DnGv 121 (by norm_num)

theorem bnd_890 : Gv 890 = 5231308662 ∧ LOG1E13LB ≤ gv 890 := by
  constructor
  · rw [Gv_eq_T 890 (by norm_num)]
    exact EqGv 122 (by norm_num)
  · rw [gv_eq_T 890 (by norm_num)]
    exact DnGv 122 (by norm_num)

theorem bnd_891 : Gv 891 = 5205890870 ∧ LOG1E13LB ≤ gv 891 := by
  constructor
  · rw [Gv_eq_T 891 (by norm_num)]
    exact EqGv 123 (by norm_num)
  · rw [gv_eq_T 891 (by norm_num)]
    exact DnGv 123 (by norm_num)

theorem bnd_892 : Gv 892 = 5167574414 ∧ LOG1E13LB ≤ gv 892 := by
  constructor
  · rw [Gv_eq_T 892 (by norm_num)]
    exact EqGv 124 (by norm_num)
  · rw [gv_eq_T 892 (by norm_num)]
    exact DnGv 124 (by norm_num)

theorem bnd_893 : Gv 893 = 5116779460 ∧ LOG1E13LB ≤ gv 893 := by
  constructor
  · rw [Gv_eq_T 893 (by norm_num)]
    exact EqGv 125 (by norm_num)
  · rw [gv_eq_T 893 (by norm_num)]
    exact DnGv 125 (by norm_num)

theorem bnd_894 : Gv 894 = 5054058860 ∧ LOG1E13LB ≤ gv 894 := by
  constructor
  · rw [Gv_eq_T 894 (by norm_num)]
    exact EqGv 126 (by norm_num)
  · rw [gv_eq_T 894 (by norm_num)]
    exact DnGv 126 (by norm_num)

theorem bnd_895 : Gv 895 = 4980006646 ∧ LOG1E13LB ≤ gv 895 := by
  constructor
  · rw [Gv_eq_T 895 (by norm_num)]
    exact EqGv 127 (by norm_num)
  · rw [gv_eq_T 895 (by norm_num)]
    exact DnGv 127 (by norm_num)

theorem bnd_896 : Gv 896 = 4895326002 ∧ LOG1E13LB ≤ gv 896 := by
  constructor
  · rw [Gv_eq_T 896 (by norm_num)]
    exact EqHv 0 (by norm_num)
  · rw [gv_eq_T 896 (by norm_num)]
    exact DnHv 0 (by norm_num)

theorem bnd_897 : Gv 897 = 4800814388 ∧ LOG1E13LB ≤ gv 897 := by
  constructor
  · rw [Gv_eq_T 897 (by norm_num)]
    exact EqHv 1 (by norm_num)
  · rw [gv_eq_T 897 (by norm_num)]
    exact DnHv 1 (by norm_num)

theorem bnd_898 : Gv 898 = 4697285602 ∧ LOG1E13LB ≤ gv 898 := by
  constructor
  · rw [Gv_eq_T 898 (by norm_num)]
    exact EqHv 2 (by norm_num)
  · rw [gv_eq_T 898 (by norm_num)]
    exact DnHv 2 (by norm_num)

theorem bnd_899 : Gv 899 = 4585607666 ∧ LOG1E13LB ≤ gv 899 := by
  constructor
  · rw [Gv_eq_T 899 (by norm_num)]
    exact EqHv 3 (by norm_num)
  · rw [gv_eq_T 899 (by norm_num)]
    exact DnHv 3 (by norm_num)

theorem bnd_900 : Gv 900 = 4466693542 ∧ LOG1E13LB ≤ gv 900 := by
  constructor
  · rw [Gv_eq_T 900 (by norm_num)]
    exact EqHv 4 (by norm_num)
  · rw [gv_eq_T 900 (by norm_num)]
    exact DnHv 4 (by norm_num)

theorem bnd_901 : Gv 901 = 4341405504 ∧ LOG1E13LB ≤ gv 901 := by
  constructor
  · rw [Gv_eq_T 901 (by norm_num)]
    exact EqHv 5 (by norm_num)
  · rw [gv_eq_T 901 (by norm_num)]
    exact DnHv 5 (by norm_num)

theorem bnd_902 : Gv 902 = 4210689260 ∧ LOG1E13LB ≤ gv 902 := by
  constructor
  · rw [Gv_eq_T 902 (by norm_num)]
    exact EqHv 6 (by norm_num)
  · rw [gv_eq_T 902 (by norm_num)]
    exact DnHv 6 (by norm_num)

theorem bnd_903 : Gv 903 = 4075424472 ∧ LOG1E13LB ≤ gv 903 := by
  constructor
  · rw [Gv_eq_T 903 (by norm_num)]
    exact EqHv 7 (by norm_num)
  · rw [gv_eq_T 903 (by norm_num)]
    exact DnHv 7 (by norm_num)

theorem bnd_904 : Gv 904 = 3936504118 ∧ LOG1E13LB ≤ gv 904 := by
  constructor
  · rw [Gv_eq_T 904 (by norm_num)]
    exact EqHv 8 (by norm_num)
  · rw [gv_eq_T 904 (by norm_num)]
    exact DnHv 8 (by norm_num)

theorem bnd_905 : Gv 905 = 3794733940 ∧ LOG1E13LB ≤ gv 905 := by
  constructor
  · rw [Gv_eq_T 905 (by norm_num)]
    exact EqHv 9 (by norm_num)
  · rw [gv_eq_T 905 (by norm_num)]
    exact DnHv 9 (by norm_num)

theorem bnd_906 : Gv 906 = 3650930734 ∧ LOG1E13LB ≤ gv 906 := by
  constructor
  · rw [Gv_eq_T 906 (by norm_num)]
    exact EqHv 10 (by norm_num)
  · rw [gv_eq_T 906 (by norm_num)]
    exact DnHv 10 (by norm_num)

theorem bnd_907 : Gv 907 = 3505839056 ∧ LOG1E13LB ≤ gv 907 := by
  constructor
  · rw [Gv_eq_T 907 (by norm_num)]
    exact EqHv 11 (by norm_num)
  · rw [gv_eq_T 907 (by norm_num)]
    exact DnHv 11 (by norm_num)

theorem bnd_908 : Gv 908 = 3360188614 ∧ LOG1E13LB ≤ gv 908 := by
  constructor
  · rw [Gv_eq_T 908 (by norm_num)]
    exact EqHv 12 (by norm_num)
  · rw [gv_eq_T 908 (by norm_num)]
    exact DnHv 12 (by norm_num)

theorem bnd_909 : Gv 909 = 3214634894 ∧ LOG1E13LB ≤ gv 909 := by
  constructor
  · rw [Gv_eq_T 909 (by norm_num)]
    exact EqHv 13 (by norm_num)
  · rw [gv_eq_T 909 (by norm_num)]
    exact DnHv 13 (by norm_num)

theorem bnd_910 : Gv 910 = 3069784938 ∧ LOG1E13LB ≤ gv 910 := by
  constructor
  · rw [Gv_eq_T 910 (by norm_num)]
    exact EqHv 14 (by norm_num)
  · rw [gv_eq_T 910 (by norm_num)]
    exact DnHv 14 (by norm_num)

theorem bnd_911 : Gv 911 = 2926152840 ∧ LOG1E13LB ≤ gv 911 := by
  constructor
  · rw [Gv_eq_T 911 (by norm_num)]
    exact EqHv 15 (by norm_num)
  · rw [gv_eq_T 911 (by norm_num)]
    exact DnHv 15 (by norm_num)

theorem bnd_912 : Gv 912 = 2784222090 ∧ LOG1E13LB ≤ gv 912 := by
  constructor
  · rw [Gv_eq_T 912 (by norm_num)]
    exact EqHv 16 (by norm_num)
  · rw [gv_eq_T 912 (by norm_num)]
    exact DnHv 16 (by norm_num)

theorem bnd_913 : Gv 913 = 2644458730 ∧ LOG1E13LB ≤ gv 913 := by
  constructor
  · rw [Gv_eq_T 913 (by norm_num)]
    exact EqHv 17 (by norm_num)
  · rw [gv_eq_T 913 (by norm_num)]
    exact DnHv 17 (by norm_num)

theorem bnd_914 : Gv 914 = 2507229418 ∧ LOG1E13LB ≤ gv 914 := by
  constructor
  · rw [Gv_eq_T 914 (by norm_num)]
    exact EqHv 18 (by norm_num)
  · rw [gv_eq_T 914 (by norm_num)]
    exact DnHv 18 (by norm_num)

theorem bnd_915 : Gv 915 = 2372783446 ∧ LOG1E13LB ≤ gv 915 := by
  constructor
  · rw [Gv_eq_T 915 (by norm_num)]
    exact EqHv 19 (by norm_num)
  · rw [gv_eq_T 915 (by norm_num)]
    exact DnHv 19 (by norm_num)

theorem bnd_916 : Gv 916 = 2241432054 ∧ LOG1E13LB ≤ gv 916 := by
  constructor
  · rw [Gv_eq_T 916 (by norm_num)]
    exact EqHv 20 (by norm_num)
  · rw [gv_eq_T 916 (by norm_num)]
    exact DnHv 20 (by norm_num)

theorem bnd_917 : Gv 917 = 2113297780 ∧ LOG1E13LB ≤ gv 917 := by
  constructor
  · rw [Gv_eq_T 917 (by norm_num)]
    exact EqHv 21 (by norm_num)
  · rw [gv_eq_T 917 (by norm_num)]
    exact DnHv 21 (by norm_num)

theorem bnd_918 : Gv 918 = 1988569538 ∧ LOG1E13LB ≤ gv 918 := by
  constructor
  · rw [Gv_eq_T 918 (by norm_num)]
    exact EqHv 22 (by norm_num)
  · rw [gv_eq_T 918 (by norm_num)]
    exact DnHv 22 (by norm_num)

theorem bnd_919 : Gv 919 = 1867275880 ∧ LOG1E13LB ≤ gv 919 := by
  constructor
  · rw [Gv_eq_T 919 (by norm_num)]
    exact EqHv 23 (by norm_num)
  · rw [gv_eq_T 919 (by norm_num)]
    exact DnHv 23 (by norm_num)

theorem bnd_920 : Gv 920 = 1749422400 ∧ LOG1E13LB ≤ gv 920 := by
  constructor
  · rw [Gv_eq_T 920 (by norm_num)]
    exact EqHv 24 (by norm_num)
  · rw [gv_eq_T 920 (by norm_num)]
    exact DnHv 24 (by norm_num)

theorem bnd_921 : Gv 921 = 1634963646 ∧ LOG1E13LB ≤ gv 921 := by
  constructor
  · rw [Gv_eq_T 921 (by norm_num)]
    exact EqHv 25 (by norm_num)
  · rw [gv_eq_T 921 (by norm_num)]
    exact DnHv 25 (by norm_num)

theorem bnd_922 : Gv 922 = 1523800150 ∧ LOG1E13LB ≤ gv 922 := by
  constructor
  · rw [Gv_eq_T 922 (by norm_num)]
    exact EqHv 26 (by norm_num)
  · rw [gv_eq_T 922 (by norm_num)]
    exact DnHv 26 (by norm_num)

theorem bnd_923 : Gv 923 = 1415762068 ∧ LOG1E13LB ≤ gv 923 := by
  constructor
  · rw [Gv_eq_T 923 (by norm_num)]
    exact EqHv 27 (by norm_num)
  · rw [gv_eq_T 923 (by norm_num)]
    exact DnHv 27 (by norm_num)

theorem bnd_924 : Gv 924 = 1310646082 ∧ LOG1E13LB ≤ gv 924 := by
  constructor
  · rw [Gv_eq_T 924 (by norm_num)]
    exact EqHv 28 (by norm_num)
  · rw [gv_eq_T 924 (by norm_num)]
    exact DnHv 28 (by norm_num)

theorem bnd_925 : Gv 925 = 1208197950 ∧ LOG1E13LB ≤ gv 925 := by
  constructor
  · rw [Gv_eq_T 925 (by norm_num)]
    exact EqHv 29 (by norm_num)
  · rw [gv_eq_T 925 (by norm_num)]
    exact DnHv 29 (by norm_num)

theorem bnd_926 : Gv 926 = 1108093910 ∧ LOG1E13LB ≤ gv 926 := by
  constructor
  · rw [Gv_eq_T 926 (by norm_num)]
    exact EqHv 30 (by norm_num)
  · rw [gv_eq_T 926 (by norm_num)]
    exact DnHv 30 (by norm_num)

theorem bnd_927 : Gv 927 = 1009962982 ∧ LOG1E13LB ≤ gv 927 := by
  constructor
  · rw [Gv_eq_T 927 (by norm_num)]
    exact EqHv 31 (by norm_num)
  · rw [gv_eq_T 927 (by norm_num)]
    exact DnHv 31 (by norm_num)

theorem bnd_928 : Gv 928 = 913456306 ∧ LOG1E13LB ≤ gv 928 := by
  constructor
  · rw [Gv_eq_T 928 (by norm_num)]
    exact EqHv 32 (by norm_num)
  · rw [gv_eq_T 928 (by norm_num)]
    exact DnHv 32 (by norm_num)

theorem bnd_929 : Gv 929 = 818167630 ∧ LOG1E13LB ≤ gv 929 := by
  constructor
  · rw [Gv_eq_T 929 (by norm_num)]
    exact EqHv 33 (by norm_num)
  · rw [gv_eq_T 929 (by norm_num)]
    exact DnHv 33 (by norm_num)

theorem bnd_930 : Gv 930 = 723626750 ∧ LOG1E13LB ≤ gv 930 := by
  constructor
  · rw [Gv_eq_T 930 (by norm_num)]
    exact EqHv 34 (by norm_num)
  · rw [gv_eq_T 930 (by norm_num)]
    exact DnHv 34 (by norm_num)

theorem bnd_931 : Gv 931 = 629432174 ∧ LOG1E13LB ≤ gv 931 := by
  constructor
  · rw [Gv_eq_T 931 (by norm_num)]
    exact EqHv 35 (by norm_num)
  · rw [gv_eq_T 931 (by norm_num)]
    exact DnHv 35 (by norm_num)

theorem bnd_932 : Gv 932 = 535087704 ∧ LOG1E13LB ≤ gv 932 := by
  constructor
  · rw [Gv_eq_T 932 (by norm_num)]
    exact EqHv 36 (by norm_num)
  · rw [gv_eq_T 932 (by norm_num)]
    exact DnHv 36 (by norm_num)

theorem bnd_933 : Gv 933 = 440124528 ∧ LOG1E13LB ≤ gv 933 := by
  constructor
  · rw [Gv_eq_T 933 (by norm_num)]
    exact EqHv 37 (by norm_num)
  · rw [gv_eq_T 933 (by norm_num)]
    exact DnHv 37 (by norm_num)

theorem bnd_934 : Gv 934 = 344069862 ∧ LOG1E13LB ≤ gv 934 := by
  constructor
  · rw [Gv_eq_T 934 (by norm_num)]
    exact EqHv 38 (by norm_num)
  · rw [gv_eq_T 934 (by norm_num)]
    exact DnHv 38 (by norm_num)

theorem bnd_935 : Gv 935 = 246493640 ∧ LOG1E13LB ≤ gv 935 := by
  constructor
  · rw [Gv_eq_T 935 (by norm_num)]
    exact EqHv 39 (by norm_num)
  · rw [gv_eq_T 935 (by norm_num)]
    exact DnHv 39 (by norm_num)

theorem bnd_936 : Gv 936 = 146929082 ∧ LOG1E13LB ≤ gv 936 := by
  constructor
  · rw [Gv_eq_T 936 (by norm_num)]
    exact EqHv 40 (by norm_num)
  · rw [gv_eq_T 936 (by norm_num)]
    exact DnHv 40 (by norm_num)

theorem bnd_937 : Gv 937 = 44980302 ∧ LOG1E13LB ≤ gv 937 := by
  constructor
  · rw [Gv_eq_T 937 (by norm_num)]
    exact EqHv 41 (by norm_num)
  · rw [gv_eq_T 937 (by norm_num)]
    exact DnHv 41 (by norm_num)

theorem bnd_938 : Gv 938 = -59798010 ∧ LOG1E13LB ≤ gv 938 := by
  constructor
  · rw [Gv_eq_T 938 (by norm_num)]
    exact EqHv 42 (by norm_num)
  · rw [gv_eq_T 938 (by norm_num)]
    exact DnHv 42 (by norm_num)

theorem bnd_939 : Gv 939 = -167759860 ∧ LOG1E13LB ≤ gv 939 := by
  constructor
  · rw [Gv_eq_T 939 (by norm_num)]
    exact EqHv 43 (by norm_num)
  · rw [gv_eq_T 939 (by norm_num)]
    exact DnHv 43 (by norm_num)

theorem bnd_940 : Gv 940 = -279257154 ∧ LOG1E13LB ≤ gv 940 := by
  constructor
  · rw [Gv_eq_T 940 (by norm_num)]
    exact EqHv 44 (by norm_num)
  · rw [gv_eq_T 940 (by norm_num)]
    exact DnHv 44 (by norm_num)

theorem bnd_941 : Gv 941 = -394604882 ∧ LOG1E13LB ≤ gv 941 := by
  constructor
  · rw [Gv_eq_T 941 (by norm_num)]
    exact EqHv 45 (by norm_num)
  · rw [gv_eq_T 941 (by norm_num)]
    exact DnHv 45 (by norm_num)

theorem bnd_942 : Gv 942 = -514105392 ∧ LOG1E13LB ≤ gv 942 := by
  constructor
  · rw [Gv_eq_T 942 (by norm_num)]
    exact EqHv 46 (by norm_num)
  · rw [gv_eq_T 942 (by norm_num)]
    exact DnHv 46 (by norm_num)

theorem bnd_943 : Gv 943 = -638028540 ∧ LOG1E13LB ≤ gv 943 := by
  constructor
  · rw [Gv_eq_T 943 (by norm_num)]
    exact EqHv 47 (by norm_num)
  · rw [gv_eq_T 943 (by norm_num)]
    exact DnHv 47 (by norm_num)

theorem bnd_944 : Gv 944 = -766555254 ∧ LOG1E13LB ≤ gv 944 := by
  constructor
  · rw [Gv_eq_T 944 (by norm_num)]
    exact EqHv 48 (by norm_num)
  · rw [gv_eq_T 944 (by norm_num)]
    exact DnHv 48 (by norm_num)

theorem bnd_945 : Gv 945 = -899897288 ∧ LOG1E13LB ≤ gv 945 := by
  constructor
  · rw [Gv_eq_T 945 (by norm_num)]
    exact EqHv 49 (by norm_num)
  · rw [gv_eq_T 945 (by norm_num)]
    exact DnHv 49 (by norm_num)

theorem bnd_946 : Gv 946 = -1038252654 ∧ LOG1E13LB ≤ gv 946 := by
  constructor
  · rw [Gv_eq_T 946 (by norm_num)]
    exact EqHv 50 (by norm_num)
  · rw [gv_eq_T 946 (by norm_num)]
    exact DnHv 50 (by norm_num)

theorem bnd_947 : Gv 947 = -1181730298 ∧ LOG1E13LB ≤ gv 947 := by
  constructor
  · rw [Gv_eq_T 947 (by norm_num)]
    exact EqHv 51 (by norm_num)
  · rw [gv_eq_T 947 (by norm_num)]
    exact DnHv 51 (by norm_num)

theorem bnd_948 : Gv 948 = -1330465152 ∧ LOG1E13LB ≤ gv 948 := by
  constructor
  · rw [Gv_eq_T 948 (by norm_num)]
    exact EqHv 52 (by norm_num)
  · rw [gv_eq_T 948 (by norm_num)]
    exact DnHv 52 (by norm_num)

theorem bnd_949 : Gv 949 = -1484606982 ∧ LOG1E13LB ≤ gv 949 := by
  constructor
  · rw [Gv_eq_T 949 (by norm_num)]
    exact EqHv 53 (by norm_num)
  · rw [gv_eq_T 949 (by norm_num)]
    exact DnHv 53 (by norm_num)

theorem bnd_950 : Gv 950 = -1644191362 ∧ LOG1E13LB ≤ gv 950 := by
  constructor
  · rw [Gv_eq_T 950 (by norm_num)]
    exact EqHv 54 (by norm_num)
  · rw [gv_eq_T 950 (by norm_num)]
    exact DnHv 54 (by norm_num)

theorem bnd_951 : Gv 951 = -1809366446 ∧ LOG1E13LB ≤ gv 951 := by
  constructor
  · rw [Gv_eq_T 951 (by norm_num)]
    exact EqHv 55 (by norm_num)
  · rw [gv_eq_T 951 (by norm_num)]
    exact DnHv 55 (by norm_num)

theorem bnd_952 : Gv 952 = -1980184004 ∧ LOG1E13LB ≤ gv 952 := by
  constructor
  · rw [Gv_eq_T 952 (by norm_num)]
    exact EqHv 56 (by norm_num)
  · rw [gv_eq_T 952 (by norm_num)]
    exact DnHv 56 (by norm_num)

theorem bnd_953 : Gv 953 = -2156752418 ∧ LOG1E13LB ≤ gv 953 := by
  constructor
  · rw [Gv_eq_T 953 (by norm_num)]
    exact EqHv 57 (by norm_num)
  · rw [gv_eq_T 953 (by norm_num)]
    exact DnHv 57 (by norm_num)

theorem bnd_954 : Gv 954 = -2339151082 ∧ LOG1E13LB ≤ gv 954 := by
  constructor
  · rw [Gv_eq_T 954 (by norm_num)]
    exact EqHv 58 (by norm_num)
  · rw [gv_eq_T 954 (by norm_num)]
    exact DnHv 58 (by norm_num)

theorem bnd_955 : Gv 955 = -2527488580 ∧ LOG1E13LB ≤ gv 955 := by
  constructor
  · rw [Gv_eq_T 955 (by norm_num)]
    exact EqHv 59 (by norm_num)
  · rw [gv_eq_T 955 (by norm_num)]
    exact DnHv 59 (by norm_num)

theorem bnd_956 : Gv 956 = -2721872472 ∧ LOG1E13LB ≤ gv 956 := by
  constructor
  · rw [Gv_eq_T 956 (by norm_num)]
    exact EqHv 60 (by norm_num)
  · rw [gv_eq_T 956 (by norm_num)]
    exact DnHv 60 (by norm_num)

theorem bnd_957 : Gv 957 = -2922439804 ∧ LOG1E13LB ≤ gv 957 := by
  constructor
  · rw [Gv_eq_T 957 (by norm_num)]
    exact EqHv 61 (by norm_num)
  · rw [gv_eq_T 957 (by norm_num)]
    exact DnHv 61 (by norm_num)

theorem bnd_958 : Gv 958 = -3129335142 ∧ LOG1E13LB ≤ gv 958 := by
  constructor
  · rw [Gv_eq_T 958 (by norm_num)]
    exact EqHv 62 (by norm_num)
  · rw [gv_eq_T 958 (by norm_num)]
    exact DnHv 62 (by norm_num)

theorem bnd_959 : Gv 959 = -3342740014 ∧ LOG1E13LB ≤ gv 959 := by
  constructor
  · rw [Gv_eq_T 959 (by norm_num)]
    exact EqHv 63 (by norm_num)
  · rw [gv_eq_T 959 (by norm_num)]
    exact DnHv 63 (by norm_num)

theorem bnd_960 : Gv 960 = -3562739502 ∧ LOG1E13LB ≤ gv 960 := by
  constructor
  · rw [Gv_eq_T 960 (by norm_num)]
    exact EqHv 64 (by norm_num)
  · rw [gv_eq_T 960 (by norm_num)]
    exact DnHv 64 (by norm_num)

theorem bnd_961 : Gv 961 = -3789611070 ∧ LOG1E13LB ≤ gv 961 := by
  constructor
  · rw [Gv_eq_T 961 (by norm_num)]
    exact EqHv 65 (by norm_num)
  · rw [gv_eq_T 961 (by norm_num)]
    exact DnHv 65 (by norm_num)

theorem bnd_962 : Gv 962 = -4023544552 ∧ LOG1E13LB ≤ gv 962 := by
  constructor
  · rw [Gv_eq_T 962 (by norm_num)]
    exact EqHv 66 (by norm_num)
  · rw [gv_eq_T 962 (by norm_num)]
    exact DnHv 66 (by norm_num)

theorem bnd_963 : Gv 963 = -4264721244 ∧ LOG1E13LB ≤ gv 963 := by
  constructor
  · rw [Gv_eq_T 963 (by norm_num)]
    exact EqHv 67 (by norm_num)
  · rw [gv_eq_T 963 (by norm_num)]
    exact DnHv 67 (by norm_num)

theorem bnd_964 : Gv 964 = -4513406146 ∧ LOG1E13LB ≤ gv 964 := by
  constructor
  · rw [Gv_eq_T 964 (by norm_num)]
    exact EqHv 68 (by norm_num)
  · rw [gv_eq_T 964 (by norm_num)]
    exact DnHv 68 (by norm_num)

theorem bnd_965 : Gv 965 = -4769840020 ∧ LOG1E13LB ≤ gv 965 := by
  constructor
  · rw [Gv_eq_T 965 (by norm_num)]
    exact EqHv 69 (by norm_num)
  · rw [gv_eq_T 965 (by norm_num)]
    exact DnHv 69 (by norm_num)

theorem bnd_966 : Gv 966 = -5034276454 ∧ LOG1E13LB ≤ gv 966 := by
  constructor
  · rw [Gv_eq_T 966 (by norm_num)]
    exact EqHv 70 (by norm_num)
  · rw [gv_eq_T 966 (by norm_num)]
    exact DnHv 70 (by norm_num)

theorem bnd_967 : Gv 967 = -5306955744 ∧ LOG1E13LB ≤ gv 967 := by
  constructor
  · rw [Gv_eq_T 967 (by norm_num)]
    exact EqHv 71 (by norm_num)
  · rw [gv_eq_T 967 (by norm_num)]
    exact DnHv 71 (by norm_num)

theorem bnd_968 : Gv 968 = -5588193668 ∧ LOG1E13LB ≤ gv 968 := by
  constructor
  · rw [Gv_eq_T 968 (by norm_num)]
    exact EqHv 72 (by norm_num)
  · rw [gv_eq_T 968 (by norm_num)]
    exact DnHv 72 (by norm_num)

theorem bnd_969 : Gv 969 = -5878237750 ∧ LOG1E13LB ≤ gv 969 := by
  constructor
  · rw [Gv_eq_T 969 (by norm_num)]
    exact EqHv 73 (by norm_num)
  · rw [gv_eq_T 969 (by norm_num)]
    exact DnHv 73 (by norm_num)

theorem bnd_970 : Gv 970 = -6177366510 ∧ LOG1E13LB ≤ gv 970 := by
  constructor
  · rw [Gv_eq_T 970 (by norm_num)]
    exact EqHv 74 (by norm_num)
  · rw [gv_eq_T 970 (by norm_num)]
    exact DnHv 74 (by norm_num)

theorem bnd_971 : Gv 971 = -6485877838 ∧ LOG1E13LB ≤ gv 971 := by
  constructor
  · rw [Gv_eq_T 971 (by norm_num)]
    exact EqHv 75 (by norm_num)
  · rw [gv_eq_T 971 (by norm_num)]
    exact DnHv 75 (by norm_num)

theorem bnd_972 : Gv 972 = -6804018790 ∧ LOG1E13LB ≤ gv 972 := by
  constructor
  · rw [Gv_eq_T 972 (by norm_num)]
    exact EqHv 76 (by norm_num)
  · rw [gv_eq_T 972 (by norm_num)]
    exact DnHv 76 (by norm_num)

theorem bnd_973 : Gv 973 = -7132134274 ∧ LOG1E13LB ≤ gv 973 := by
  constructor
  · rw [Gv_eq_T 973 (by norm_num)]
    exact EqHv 77 (by norm_num)
  · rw [gv_eq_T 973 (by norm_num)]
    exact DnHv 77 (by norm_num)

theorem bnd_974 : Gv 974 = -7470461546 ∧ LOG1E13LB ≤ gv 974 := by
  constructor
  · rw [Gv_eq_T 974 (by norm_num)]
    exact EqHv 78 (by norm_num)
  · rw [gv_eq_T 974 (by norm_num)]
    exact DnHv 78 (by norm_num)

theorem bnd_975 : Gv 975 = -7819274734 ∧ LOG1E13LB ≤ gv 975 := by
  constructor
  · rw [Gv_eq_T 975 (by norm_num)]
    exact EqHv 79 (by norm_num)
  · rw [gv_eq_T 975 (by norm_num)]
    exact DnHv 79 (by norm_num)

theorem bnd_976 : Gv 976 = -8178879076 ∧ LOG1E13LB ≤ gv 976 := by
  constructor
  · rw [Gv_eq_T 976 (by norm_num)]
    exact EqHv 80 (by norm_num)
  · rw [gv_eq_T 976 (by norm_num)]
    exact DnHv 80 (by norm_num)

theorem bnd_977 : Gv 977 = -8549558162 ∧ LOG1E13LB ≤ gv 977 := by
  constructor
  · rw [Gv_eq_T 977 (by norm_num)]
    exact EqHv 81 (by norm_num)
  · rw [gv_eq_T 977 (by norm_num)]
    exact DnHv 81 (by norm_num)

theorem bnd_978 : Gv 978 = -8931526322 ∧ LOG1E13LB ≤ gv 978 := by
  constructor
  · rw [Gv_eq_T 978 (by norm_num)]
    exact EqHv 82 (by norm_num)
  · rw [gv_eq_T 978 (by norm_num)]
    exact DnHv 82 (by norm_num)

theorem bnd_979 : Gv 979 = -9325054516 ∧ LOG1E13LB ≤ gv 979 := by
  constructor
  · rw [Gv_eq_T 979 (by norm_num)]
    exact EqHv 83 (by norm_num)
  · rw [gv_eq_T 979 (by norm_num)]
    exact DnHv 83 (by norm_num)

theorem bnd_980 : Gv 980 = -9730402826 ∧ LOG1E13LB ≤ gv 980 := by
  constructor
  · rw [Gv_eq_T 980 (by norm_num)]
    exact EqHv 84 (by norm_num)
  · rw [gv_eq_T 980 (by norm_num)]
    exact DnHv 84 (by norm_num)

theorem bnd_981 : Gv 981 = -10147760018 ∧ LOG1E13LB ≤ gv 981 := by
  constructor
  · rw [Gv_eq_T 981 (by norm_num)]
    exact EqHv 85 (by norm_num)
  · rw [gv_eq_T 981 (by norm_num)]
    exact DnHv 85 (by norm_num)

theorem bnd_982 : Gv 982 = -10577327756 ∧ LOG1E13LB ≤ gv 982 := by
  constructor
  · rw [Gv_eq_T 982 (by norm_num)]
    exact EqHv 86 (by norm_num)
  · rw [gv_eq_T 982 (by norm_num)]
    exact DnHv 86 (by norm_num)

theorem bnd_983 : Gv 983 = -11019310454 ∧ LOG1E13LB ≤ gv 983 := by
  constructor
  · rw [Gv_eq_T 983 (by norm_num)]
    exact EqHv 87 (by norm_num)
  · rw [gv_eq_T 983 (by norm_num)]
    exact DnHv 87 (by norm_num)

theorem bnd_984 : Gv 984 = -11473822048 ∧ LOG1E13LB ≤ gv 984 := by
  constructor
  · rw [Gv_eq_T 984 (by norm_num)]
    exact EqHv 88 (by norm_num)
  · rw [gv_eq_T 984 (by norm_num)]
    exact DnHv 88 (by norm_num)

theorem bnd_985 : Gv 985 = -11940979216 ∧ LOG1E13LB ≤ gv 985 := by
  constructor
  · rw [Gv_eq_T 985 (by norm_num)]
    exact EqHv 89 (by norm_num)
  · rw [gv_eq_T 985 (by norm_num)]
    exact DnHv 89 (by norm_num)

theorem bnd_986 : Gv 986 = -12420860720 ∧ LOG1E13LB ≤ gv 986 := by
  constructor
  · rw [Gv_eq_T 986 (by norm_num)]
    exact EqHv 90 (by norm_num)
  · rw [gv_eq_T 986 (by norm_num)]
    exact DnHv 90 (by norm_num)

theorem bnd_987 : Gv 987 = -12913483446 ∧ LOG1E13LB ≤ gv 987 := by
  constructor
  · rw [Gv_eq_T 987 (by norm_num)]
    exact EqHv 91 (by norm_num)
  · rw [gv_eq_T 987 (by norm_num)]
    exact DnHv 91 (by norm_num)

theorem bnd_988 : Gv 988 = -13418771300 ∧ LOG1E13LB ≤ gv 988 := by
  constructor
  · rw [Gv_eq_T 988 (by norm_num)]
    exact EqHv 92 (by norm_num)
  · rw [gv_eq_T 988 (by norm_num)]
    exact DnHv 92 (by norm_num)

theorem bnd_989 : Gv 989 = -13936715098 ∧ LOG1E13LB ≤ gv 989 := by
  constructor
  · rw [Gv_eq_T 989 (by norm_num)]
    exact EqHv 93 (by norm_num)
  · rw [gv_eq_T 989 (by norm_num)]
    exact DnHv 93 (by norm_num)

theorem bnd_990 : Gv 990 = -14467104326 ∧ LOG1E13LB ≤ gv 990 := by
  constructor
  · rw [Gv_eq_T 990 (by norm_num)]
    exact EqHv 94 (by norm_num)
  · rw [gv_eq_T 990 (by norm_num)]
    exact DnHv 94 (by norm_num)

theorem bnd_991 : Gv 991 = -15009691062 ∧ LOG1E13LB ≤ gv 991 := by
  constructor
  · rw [Gv_eq_T 991 (by norm_num)]
    exact EqHv 95 (by norm_num)
  · rw [gv_eq_T 991 (by norm_num)]
    exact DnHv 95 (by norm_num)

theorem bnd_992 : Gv 992 = -15564160810 ∧ LOG1E13LB ≤ gv 992 := by
  constructor
  · rw [Gv_eq_T 992 (by norm_num)]
    exact EqHv 96 (by norm_num)
  · rw [gv_eq_T 992 (by norm_num)]
    exact DnHv 96 (by norm_num)

theorem bnd_993 : Gv 993 = -16130085098 ∧ LOG1E13LB ≤ gv 993 := by
  constructor
  · rw [Gv_eq_T 993 (by norm_num)]
    exact EqHv 97 (by norm_num)
  · rw [gv_eq_T 993 (by norm_num)]
    exact DnHv 97 (by norm_num)

theorem bnd_994 : Gv 994 = -16706955938 ∧ LOG1E13LB ≤ gv 994 := by
  constructor
  · rw [Gv_eq_T 994 (by norm_num)]
    exact EqHv 98 (by norm_num)
  · rw [gv_eq_T 994 (by norm_num)]
    exact DnHv 98 (by norm_num)

theorem bnd_995 : Gv 995 = -17294152994 ∧ LOG1E13LB ≤ gv 995 := by
  constructor
  · rw [Gv_eq_T 995 (by norm_num)]
    exact EqHv 99 (by norm_num)
  · rw [gv_eq_T 995 (by norm_num)]
    exact DnHv 99 (by norm_num)

theorem bnd_996 : Gv 996 = -17890877412 ∧ LOG1E13LB ≤ gv 996 := by
  constructor
  · rw [Gv_eq_T 996 (by norm_num)]
    exact EqHv 100 (by norm_num)
  · rw [gv_eq_T 996 (by norm_num)]
    exact DnHv 100 (by norm_num)

theorem bnd_997 : Gv 997 = -18496253622 ∧ LOG1E13LB ≤ gv 997 := by
  constructor
  · rw [Gv_eq_T 997 (by norm_num)]
    exact EqHv 101 (by norm_num)
  · rw [gv_eq_T 997 (by norm_num)]
    exact DnHv 101 (by norm_num)

theorem bnd_998 : Gv 998 = -19109232818 ∧ LOG1E13LB ≤ gv 998 := by
  constructor
  · rw [Gv_eq_T 998 (by norm_num)]
    exact EqHv 102 (by norm_num)
  · rw [gv_eq_T 998 (by norm_num)]
    exact DnHv 102 (by norm_num)

theorem bnd_999 : Gv 999 = -19728649310 ∧ LOG1E13LB ≤ gv 999 := by
  constructor
  · rw [Gv_eq_T 999 (by norm_num)]
    exact EqHv 103 (by norm_num)
  · rw [gv_eq_T 999 (by norm_num)]
    exact DnHv 103 (by norm_num)

theorem bnd_1000 : Gv 1000 = -20353135154 ∧ LOG1E13LB ≤ gv 1000 := by
  constructor
  · rw [Gv_eq_T 1000 (by norm_num)]
    exact EqHv 104 (by norm_num)
  · rw [gv_eq_T 1000 (by norm_num)]
    exact DnHv 104 (by norm_num)

theorem bnd_1001 : Gv 1001 = -20981178428 ∧ LOG1E13LB ≤ gv 1001 := by
  constructor
  · rw [Gv_eq_T 1001 (by norm_num)]
    exact EqHv 105 (by norm_num)
  · rw [gv_eq_T 1001 (by norm_num)]
    exact DnHv 105 (by norm_num)

theorem bnd_1002 : Gv 1002 = -21611092554 ∧ LOG1E13LB ≤ gv 1002 := by
  constructor
  · rw [Gv_eq_T 1002 (by norm_num)]
    exact EqHv 106 (by norm_num)
  · rw [gv_eq_T 1002 (by norm_num)]
    exact DnHv 106 (by norm_num)

theorem bnd_1003 : Gv 1003 = -22241048762 ∧ LOG1E13LB ≤ gv 1003 := by
  constructor
  · rw [Gv_eq_T 1003 (by norm_num)]
    exact EqHv 107 (by norm_num)
  · rw [gv_eq_T 1003 (by norm_num)]
    exact DnHv 107 (by norm_num)

theorem bnd_1004 : Gv 1004 = -22868953082 ∧ LOG1E13LB ≤ gv 1004 := by
  constructor
  · rw [Gv_eq_T 1004 (by norm_num)]
    exact EqHv 108 (by norm_num)
  · rw [gv_eq_T 1004 (by norm_num)]
    exact DnHv 108 (by norm_num)

theorem bnd_1005 : Gv 1005 = -23492605936 ∧ LOG1E13LB ≤ gv 1005 := by
  constructor
  · rw [Gv_eq_T 1005 (by norm_num)]
    exact EqHv 109 (by norm_num)
  · rw [gv_eq_T 1005 (by norm_num)]
    exact DnHv 109 (by norm_num)

theorem bnd_1006 : Gv 1006 = -24109671438 ∧ LOG1E13LB ≤ gv 1006 := by
  constructor
  · rw [Gv_eq_T 1006 (by norm_num)]
    exact EqHv 110 (by norm_num)
  · rw [gv_eq_T 1006 (by norm_num)]
    exact DnHv 110 (by norm_num)

theorem bnd_1007 : Gv 1007 = -24717503650 ∧ LOG1E13LB ≤ gv 1007 := by
  constructor
  · rw [Gv_eq_T 1007 (by norm_num)]
    exact EqHv 111 (by norm_num)
  · rw [gv_eq_T 1007 (by norm_num)]
    exact DnHv 111 (by norm_num)

theorem bnd_1008 : Gv 1008 = -25313452758 ∧ LOG1E13LB ≤ gv 1008 := by
  constructor
  · rw [Gv_eq_T 1008 (by norm_num)]
    exact EqHv 112 (by norm_num)
  · rw [gv_eq_T 1008 (by norm_num)]
    exact DnHv 112 (by norm_num)

theorem bnd_1009 : Gv 1009 = -25894687206 ∧ LOG1E13LB ≤ gv 1009 := by
  constructor
  · rw [Gv_eq_T 1009 (by norm_num)]
    exact EqHv 113 (by norm_num)
  · rw [gv_eq_T 1009 (by norm_num)]
    exact DnHv 113 (by norm_num)

theorem bnd_1010 : Gv 1010 = -26458235702 ∧ LOG1E13LB ≤ gv 1010 := by
  constructor
  · rw [Gv_eq_T 1010 (by norm_num)]
    exact EqHv 114 (by norm_num)
  · rw [gv_eq_T 1010 (by norm_num)]
    exact DnHv 114 (by norm_num)

theorem bnd_1011 : Gv 1011 = -27001044578 ∧ LOG1E13LB ≤ gv 1011 := by
  constructor
  · rw [Gv_eq_T 1011 (by norm_num)]
    exact EqHv 115 (by norm_num)
  · rw [gv_eq_T 1011 (by norm_num)]
    exact DnHv 115 (by norm_num)

theorem bnd_1012 : Gv 1012 = -27520080910 ∧ LOG1E13LB ≤ gv 1012 := by
  constructor
  · rw [Gv_eq_T 1012 (by norm_num)]
    exact EqHv 116 (by norm_num)
  · rw [gv_eq_T 1012 (by norm_num)]
    exact DnHv 116 (by norm_num)

theorem bnd_1013 : Gv 1013 = -28012158582 ∧ LOG1E13LB ≤ gv 1013 := by
  constructor
  · rw [Gv_eq_T 1013 (by norm_num)]
    exact EqHv 117 (by norm_num)
  · rw [gv_eq_T 1013 (by norm_num)]
    exact DnHv 117 (by norm_num)

theorem bnd_1014 : Gv 1014 = -28474197204 ∧ LOG1E13LB ≤ gv 1014 := by
  constructor
  · rw [Gv_eq_T 1014 (by norm_num)]
    exact EqHv 118 (by norm_num)
  · rw [gv_eq_T 1014 (by norm_num)]
    exact DnHv 118 (by norm_num)

theorem bnd_1015 : Gv 1015 = -28903150014 ∧ LOG1E13LB ≤ gv 1015 := by
  constructor
  · rw [Gv_eq_T 1015 (by norm_num)]
    exact EqHv 119 (by norm_num)
  · rw [gv_eq_T 1015 (by norm_num)]
    exact DnHv 119 (by norm_num)

theorem bnd_1016 : Gv 1016 = -29296084514 ∧ LOG1E13LB ≤ gv 1016 := by
  constructor
  · rw [Gv_eq_T 1016 (by norm_num)]
    exact EqHv 120 (by norm_num)
  · rw [gv_eq_T 1016 (by norm_num)]
    exact DnHv 120 (by norm_num)

theorem bnd_1017 : Gv 1017 = -29650160958 ∧ LOG1E13LB ≤ gv 1017 := by
  constructor
  · rw [Gv_eq_T 1017 (by norm_num)]
    exact EqHv 121 (by norm_num)
  · rw [gv_eq_T 1017 (by norm_num)]
    exact DnHv 121 (by norm_num)

theorem bnd_1018 : Gv 1018 = -29962830998 ∧ LOG1E13LB ≤ gv 1018 := by
  constructor
  · rw [Gv_eq_T 1018 (by norm_num)]
    exact EqHv 122 (by norm_num)
  · rw [gv_eq_T 1018 (by norm_num)]
    exact DnHv 122 (by norm_num)

theorem bnd_1019 : Gv 1019 = -30231688590 ∧ LOG1E13LB ≤ gv 1019 := by
  constructor
  · rw [Gv_eq_T 1019 (by norm_num)]
    exact EqHv 123 (by norm_num)
  · rw [gv_eq_T 1019 (by norm_num)]
    exact DnHv 123 (by norm_num)

theorem bnd_1020 : Gv 1020 = -30454659130 ∧ LOG1E13LB ≤ gv 1020 := by
  constructor
  · rw [Gv_eq_T 1020 (by norm_num)]
    exact EqHv 124 (by norm_num)
  · rw [gv_eq_T 1020 (by norm_num)]
    exact DnHv 124 (by norm_num)

theorem bnd_1021 : Gv 1021 = -30629982294 ∧ LOG1E13LB ≤ gv 1021 := by
  constructor
  · rw [Gv_eq_T 1021 (by norm_num)]
    exact EqHv 125 (by norm_num)
  · rw [gv_eq_T 1021 (by norm_num)]
    exact DnHv 125 (by norm_num)

theorem bnd_1022 : Gv 1022 = -30756244438 ∧ LOG1E13LB ≤ gv 1022 := by
  constructor
  · rw [Gv_eq_T 1022 (by norm_num)]
    exact EqHv 126 (by norm_num)
  · rw [gv_eq_T 1022 (by norm_num)]
    exact DnHv 126 (by norm_num)

theorem bnd_1023 : Gv 1023 = -30832398772 ∧ LOG1E13LB ≤ gv 1023 := by
  constructor
  · rw [Gv_eq_T 1023 (by norm_num)]
    exact EqHv 127 (by norm_num)
  · rw [gv_eq_T 1023 (by norm_num)]
    exact DnHv 127 (by norm_num)

end Work.CNum
