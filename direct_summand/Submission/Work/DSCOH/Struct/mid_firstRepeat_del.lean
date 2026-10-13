import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-- Deleting the `b`-th entry of a tuple does not move the `a`-th entry, as long as `a` is strictly
to the left of `b`. -/
lemma del_apply_of_lt {n : ℕ} {ι : Type*} (x : Fin (n + 2) → ι) (b : Fin (n + 2))
    (a : Fin (n + 1)) (h : (a : ℕ) < (b : ℕ)) :
    Work.DSCOH.Norm.del x b a = x a.castSucc := by
  rw [Work.DSCOH.Norm.del_apply,
    Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]

/-- If `b` lies at least two places to the right of the first repeat `frA y` of a nondecreasing
non-strictly-increasing tuple `y`, then `frA y` is also the first repeat of `del y b`.

Indeed, both positions `frA y` and `frA y + 1` survive the deletion (and carry equal values, namely
`frV y`), while deleting `b` does not change the entries at any position below `frA y`, so a repeat
of `del y b` below `frA y` would already be a repeat of `y` below its first repeat. -/
theorem mid_firstRepeat_del {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ))
    (ha : (Work.DSCOH.Norm.frA y hy hh : ℕ) < k)
    (hz : ¬ StrictMono (Work.DSCOH.Norm.del y b)) :
    Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
        (Work.DSCOH.Norm.monotone_del y b hy) hz
      = (⟨(Work.DSCOH.Norm.frA y hy hh : ℕ), ha⟩ : Fin k) := by
  set A := Work.DSCOH.Norm.frA y hy hh with hA
  have h1' : A.val + 2 ≤ (b : ℕ) := by simpa [hA] using h1
  have ha' : A.val < k := by simpa [hA] using ha
  have hbA : A.val < (b : ℕ) := by omega
  have hbA1 : A.val + 1 < (b : ℕ) := by omega
  let a : Fin k := ⟨A.val, ha'⟩
  -- `del y b` has a repeat at the position `a` corresponding to `frA y`.
  have hrep : Work.DSCOH.Norm.del y b a.castSucc = Work.DSCOH.Norm.del y b a.succ := by
    rw [del_apply_of_lt y b a.castSucc (by simp only [Fin.val_castSucc]; omega),
      del_apply_of_lt y b a.succ (by simp only [Fin.val_succ]; omega)]
    have e1 : (a.castSucc : Fin (k + 1)).castSucc = A.castSucc := Fin.ext rfl
    have e2 : (a.succ : Fin (k + 1)).castSucc = A.succ := Fin.ext rfl
    rw [e1, e2]
    exact Work.DSCOH.Norm.firstRepeat_spec y hy hh
  -- ... and no repeat of `del y b` sits strictly to the left of `a`.
  have key : ∀ i : Fin k, Work.DSCOH.Norm.del y b i.castSucc = Work.DSCOH.Norm.del y b i.succ →
      a ≤ i := by
    intro i hi
    by_contra hcon
    have hilt : i.val < A.val := by
      have h' := Fin.lt_def.mp (not_le.mp hcon)
      simpa [a] using h'
    have hi_lt_b : i.val < (b : ℕ) := by omega
    have hi_lt_b1 : i.val + 1 < (b : ℕ) := by omega
    rw [del_apply_of_lt y b i.castSucc (by simp only [Fin.val_castSucc]; omega),
      del_apply_of_lt y b i.succ (by simp only [Fin.val_succ]; omega)] at hi
    have hp : (i.castSucc : Fin (k + 1)).succ = (i.succ).castSucc :=
      Fin.ext (by simp [Fin.val_succ])
    rw [← hp] at hi
    have hle := Work.DSCOH.Norm.firstRepeat_le y hy hh (i.castSucc) hi
    have hle' : (Work.DSCOH.Norm.firstRepeat y hy hh).val ≤ i.val := by
      have := Fin.le_def.mp hle
      simpa [Fin.val_castSucc] using this
    have : A.val ≤ i.val := by simpa [hA, Work.DSCOH.Norm.frA] using hle'
    omega
  have hXa : Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hz ≤ a :=
    Work.DSCOH.Norm.firstRepeat_le (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hz a hrep
  have haX : a ≤ Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hz :=
    key _ (Work.DSCOH.Norm.firstRepeat_spec (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hz)
  have hXeq : Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hz = a := le_antisymm hXa haX
  exact hXeq.trans (Fin.ext rfl)

end Work.DSCOH.Struct
