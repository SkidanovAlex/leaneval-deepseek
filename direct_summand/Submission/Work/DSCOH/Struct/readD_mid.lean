/-
Area DSCOH — the "middle" case of the first read index of the normalization homotopy.

For a nondecreasing tuple `y : Fin (k+2) → ι` which is not strictly increasing, `frA y` is the
position of its first repeat and `frA2 y` the last position carrying the repeated value `frV y`;
so the positions `frA y, …, frA2 y` are exactly the block of entries equal to `frV y`.

The homotopy `semiHom` reads, on a nondecreasing tuple `z`, the component of the cochain at the
index obtained by duplicating the first repeat of `z`.  Evaluating `semiHom ≫ semiD` at an index
`y` produces at the deletion position `b` the read index `readD y b` with sign `signD y b`, namely
the composite "delete `b`, then duplicate the first repeat of the deletion" (with sign
`(-1)^(b + firstRepeat (del y b))`), and `readD y b = y` in the degenerate case where `del y b` is
already strictly increasing.

`readD_mid` treats the case where the deleted position `b` lies inside the block of `frV y`, i.e.
`frA y + 2 ≤ b ≤ frA2 y`.  Then

* deleting `b` leaves the adjacent repeat `y (frA y) = y (frA y + 1)` in place, so `del y b` is
  not strictly increasing (`mid_del_notStrictMono`), and the first repeat of `del y b` is still
  `frA y` (`mid_firstRepeat_del`);
* duplicating at `frA y` then reconstructs `y` itself, because the composite
  `b.succAbove ((frA y).predAbove ·)` only moves positions inside the block `[frA y, frA2 y]`, on
  which `y` is constantly `frV y` (`mid_predAbove_swap`).

Hence `readD y b = y`, and the sign is `(-1)^(b + frA y) = (-1)^(frA y + b)`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Struct.mid_del_notStrictMono
import Submission.Work.DSCOH.Struct.mid_firstRepeat_del
import Submission.Work.DSCOH.Struct.mid_predAbove_swap

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

set_option linter.unusedSectionVars false

variable {k : ℕ} {ι : Type*} [LinearOrder ι]

/-- The position `frA y` is a legal index of `Fin k` as soon as some `b : Fin (k+2)` satisfies
`frA y + 2 ≤ b`. -/
private lemma frA_lt_of_mid (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    (b : Fin (k + 2)) (h1 : (frA y hy hh : ℕ) + 2 ≤ (b : ℕ)) :
    (frA y hy hh : ℕ) < k := by
  have := b.isLt
  omega

/-- In the middle case `frA y + 2 ≤ b ≤ frA2 y` the first read index is `y` itself and the sign is
`(-1)^(frA y + b)`. -/
theorem readD_mid {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (h1 : (Work.DSCOH.Norm.frA y hy hh : ℕ) + 2 ≤ (b : ℕ))
    (h2 : (b : ℕ) ≤ (Work.DSCOH.Norm.frA2 y hy hh : ℕ)) :
    Work.DSCOH.Norm.readD y hy hh b = y ∧
      Work.DSCOH.Norm.signD y hy hh b =
        (-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) := by
  have ha : (frA y hy hh : ℕ) < k := frA_lt_of_mid y hy hh b h1
  -- deleting `b` leaves a repeat, and the first repeat of the deletion is still `frA y`
  have hz : ¬ StrictMono (del y b) := mid_del_notStrictMono y hy hh b h1
  have hfr : firstRepeat (del y b) (monotone_del y b hy) hz = (⟨(frA y hy hh : ℕ), ha⟩ : Fin k) :=
    mid_firstRepeat_del y hy hh b h1 ha hz
  -- duplicating at `frA y` after the deletion reconstructs `y`
  have hdup : dup (del y b) (⟨(frA y hy hh : ℕ), ha⟩ : Fin k).castSucc = y := by
    funext i
    rw [show (⟨(frA y hy hh : ℕ), ha⟩ : Fin k).castSucc = frA y hy hh from Fin.ext rfl]
    simp only [dup_apply, del_apply]
    exact mid_predAbove_swap y hy hh b h1 h2 i
  constructor
  · rw [readD, dite_eq_right hz, hfr]
    exact hdup
  · rw [signD, dite_eq_right hz, hfr, Nat.add_comm]

end Work.DSCOH.Struct
