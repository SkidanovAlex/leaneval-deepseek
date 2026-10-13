/-
Area DSCOH (curric-46) — the tuple-level combinatorics of the normalization homotopy, case `b`
strictly after the first-repeat block.

For a nondecreasing tuple `y : Fin (k+2) → ι` which is not strictly increasing, let `a = frA y` be
the position of the first repeat and `frA2 y` the last position carrying the repeated value
`frV y`.  If the deletion index `b` satisfies `frA2 y < b`, then deleting position `b` does not
touch the repeat: the first repeat of `del y b` is again at position `a`.  Consequently the term of
the "first differential" read at `b` is the deletion of the `(b+1)`-st position of the tuple
`dup y a.castSucc` (which duplicates the first repeat of `y`), with the prescribed sign.

Both auxiliary steps are delegated lemmas in this directory:
* `Work.DSCOH.Struct.del_not_strictMono_gt` — `del y b` is not strictly increasing;
* `Work.DSCOH.Struct.firstRepeat_del_gt` — its first repeat is still `frA y`.
The remaining tuple identity is the pointwise index identity
`Work.DSCOH.Norm.succAbove_predAbove_gt` of `Norm/HomoDefs.lean`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Struct.del_not_strictMono_gt
import Submission.Work.DSCOH.Struct.firstRepeat_del_gt

namespace Work.DSCOH.Struct

theorem readD_gt {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (Work.DSCOH.Norm.frA2 y hy hh : ℕ) < (b : ℕ)) :
    Work.DSCOH.Norm.readD y hy hh b =
        Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y (Work.DSCOH.Norm.frA y hy hh).castSucc)
          b.succ ∧
      Work.DSCOH.Norm.signD y hy hh b =
        -(-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b.succ : ℕ)) := by
  -- The deletion of `b` leaves the first repeat of `y` intact, so `readD`/`signD` take their
  -- non-strict branch, with the first repeat still at `frA y`.
  have hns : ¬ StrictMono (Work.DSCOH.Norm.del y b) :=
    del_not_strictMono_gt y hy hh b hb
  have hfr : (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hns).castSucc = Work.DSCOH.Norm.frA y hy hh :=
    firstRepeat_del_gt y hy hh b hb hns
  have hfrv : (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
      (Work.DSCOH.Norm.monotone_del y b hy) hns : ℕ) = (Work.DSCOH.Norm.frA y hy hh : ℕ) := by
    simpa using congrArg Fin.val hfr
  -- The index hypothesis needed by the tuple identity: `frA y < b`.
  have hpb : (Work.DSCOH.Norm.frA y hy hh : ℕ) < (b : ℕ) := by
    have hle : (Work.DSCOH.Norm.frA y hy hh).succ ≤ Work.DSCOH.Norm.frA2 y hy hh := by
      have hmem : (Work.DSCOH.Norm.frA y hy hh).succ ∈
          Finset.univ.filter (fun i : Fin (k + 2) => y i = Work.DSCOH.Norm.frV y hy hh) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Work.DSCOH.Norm.firstRepeat_spec y hy hh).symm⟩
      unfold Work.DSCOH.Norm.frA2
      exact Finset.le_max' _ _ hmem
    have h2 : ((Work.DSCOH.Norm.frA y hy hh).succ : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ) :=
      Fin.le_def.mp hle
    have h3 : ((Work.DSCOH.Norm.frA y hy hh).succ : ℕ) = (Work.DSCOH.Norm.frA y hy hh : ℕ) + 1 :=
      Fin.val_succ _
    omega
  constructor
  · -- Both sides introduce, then delete, the same duplication of the entry at `frA y`.
    rw [Work.DSCOH.Norm.readD, dite_eq_right hns, hfr]
    funext i
    simp only [Work.DSCOH.Norm.dup_apply, Work.DSCOH.Norm.del_apply]
    exact congrArg y (Work.DSCOH.Norm.succAbove_predAbove_gt _ b hpb i)
  · -- The two exponents differ by one, and `-(-1) ^ (m+1) = (-1) ^ m`.
    rw [Work.DSCOH.Norm.signD, dite_eq_right hns, hfrv]
    have hsv : (b.succ : ℕ) = (b : ℕ) + 1 := Fin.val_succ b
    rw [hsv]
    have hmix : (Work.DSCOH.Norm.frA y hy hh : ℕ) + ((b : ℕ) + 1)
        = ((b : ℕ) + (Work.DSCOH.Norm.frA y hy hh : ℕ)) + 1 := by omega
    rw [hmix, pow_succ]
    ring

end Work.DSCOH.Struct
