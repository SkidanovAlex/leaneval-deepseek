import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Struct.frV_eq_of_between

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-! ## Index computations for the composite `b.succAbove (a.predAbove ·)`

For `a : Fin (k+1)` and `b : Fin (k+2)` with `a + 2 ≤ b`, the composite
`b.succAbove (a.predAbove ·) : Fin (k+2) → Fin (k+2)` fixes the positions `i ≤ a` and `i > b`
and subtracts one on the window `a < i ≤ b`. -/

/-- If `i ≤ a` (and `b ≥ a + 2`, so that the shifted value stays below the hole `b`), the
composite `b.succAbove (a.predAbove ·)` fixes `i`. -/
lemma succAbove_predAbove_eq_self_of_le {k : ℕ} (a : Fin (k + 1)) (b : Fin (k + 2))
    (i : Fin (k + 2)) (h : (i : ℕ) ≤ (a : ℕ)) (hb : (a : ℕ) + 2 ≤ (b : ℕ)) :
    b.succAbove (a.predAbove i) = i := by
  ext
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- If `a < i ≤ b`, the composite `b.succAbove (a.predAbove ·)` sends `i` to the position with
value `i - 1`. -/
lemma succAbove_predAbove_val_of_between {k : ℕ} (a : Fin (k + 1)) (b : Fin (k + 2))
    (i : Fin (k + 2)) (h1 : (a : ℕ) < (i : ℕ)) (h2 : (i : ℕ) ≤ (b : ℕ)) :
    (b.succAbove (a.predAbove i) : ℕ) = (i : ℕ) - 1 := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- If `i > b` (and `a < b`), the composite `b.succAbove (a.predAbove ·)` fixes `i`. -/
lemma succAbove_predAbove_eq_self_of_gt {k : ℕ} (a : Fin (k + 1)) (b : Fin (k + 2))
    (i : Fin (k + 2)) (h : (b : ℕ) < (i : ℕ)) (ha : (a : ℕ) < (b : ℕ)) :
    b.succAbove (a.predAbove i) = i := by
  ext
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem mid_predAbove_swap {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ))
    (h2 : (b : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ)) (i : Fin (k + 2)) :
    y (b.succAbove ((Work.DSCOH.Norm.frA y hy hh).predAbove i)) = y i := by
  rcases le_or_gt (i : ℕ) (Work.DSCOH.Norm.frA y hy hh : ℕ) with hle | hlt
  · -- `i ≤ frA`: the composite fixes `i`
    rw [succAbove_predAbove_eq_self_of_le (Work.DSCOH.Norm.frA y hy hh) b i hle h1]
  · rcases le_or_gt (i : ℕ) (b : ℕ) with hle2 | hlt2
    · -- `frA < i ≤ b`: the composite lands on the position of value `i - 1`, and both `i` and
      -- that position lie in the block `[frA, frA2]` on which `y` is constantly `frV`
      have hval := succAbove_predAbove_val_of_between (Work.DSCOH.Norm.frA y hy hh) b i hlt hle2
      have hc : y (b.succAbove ((Work.DSCOH.Norm.frA y hy hh).predAbove i)) = frV y hy hh := by
        apply frV_eq_of_between y hy hh
        · rw [hval]; omega
        · rw [hval]; omega
      rw [hc]
      exact (frV_eq_of_between y hy hh i (by omega) (by omega)).symm
    · -- `b < i`: the composite fixes `i`
      rw [succAbove_predAbove_eq_self_of_gt (Work.DSCOH.Norm.frA y hy hh) b i hlt2 (by omega)]

end Work.DSCOH.Struct
