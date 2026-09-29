import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auWinSlice

/-!
# Data shapes for the streaming window loop of `Work.Resample.auSetup`

`auSetup` must turn the input array `ofList (u.map cfxVal)` and the parameter block
`auPvals p α s t` into the window stream `auStreamV p α s t u`.  The stream is produced by a single
loop over the `t` records of the weight table, maintaining a sliding window of the extended input
array.

This module fixes the *data* the loop manipulates (nothing here is a program):

* `auWinV p α s t u k = (auWin p α s t u k).map cfxVal` is the window of round `k` as a list of
  values; `auWinRec` says that `auWinV … (k+1)` is obtained from `auWinV … k` by dropping the
  record's slide `auK s t (k+1) - auK s t k` and appending `auElem … k`.
* `auElem p α s t u k = cfxVal (auExt … [auK s t k + auL p α])` is the entry that enters the window
  when the slide is `1` (and is discarded when the slide is `0`).
* `auElems p α s t u = ((auExt p α s u).drop (auL p α)).map cfxVal` is the *element run*: the
  entries of the extended array from `auL p α` on, in order.  Its `n`-th entry (0-based, top first)
  is `auElem … n`, so a pointer that advances exactly on the slides `1` always exposes the entry the
  window wants (`auElems_getD`).
* `auSeqFlg g` (`= nil` for `g = 0`, a `cons` for `g = 1`) and `auRecF p α s t k` are the record of
  round `k` *re-encoded* so that the slide is visible to a glyph test: `auRecF` is
  `cons (auSeqFlg g) (cons (int g) (ofList (auWts … k)))` (`auRecF_eq`), and the chunk is
  `auChunkF p α s t u k = cons (ofList (auWts … k)) (ofList (auWinV … k)) = auChunk p α s t u k`
  (`auChunkF_eq`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The glyph-level flag of a slide `g` (`0` or `1`): `nil` for `0`, a `cons`-value for `1`. -/
def auSeqFlg (g : ℕ) : Val := if g = 0 then .nil else .cons .nil .nil

/-- The extended record of round `k`: the flag, the slide, the weight list. -/
def auRecF (p α s t k : ℕ) : Val :=
  .cons (auSeqFlg (auK s t (k+1) - auK s t k))
    (.cons (.int ((auK s t (k+1) : ℤ) - (auK s t k : ℤ))) (ofList (auWts p α s t k)))

/-- The extended table: the records `auRecF` of all rounds. -/
def auRecsF (p α s t : ℕ) : List Val := (List.range t).map fun k => auRecF p α s t k

/-- The window of round `k` as a list of values. -/
def auWinV (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : List Val :=
  (auWin p α s t u k).map cfxVal

/-- The entry that enters the window of round `k` when the slide is `1`. -/
def auElem (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : Val :=
  cfxVal ((auExt p α s u).getD (auL p α + auK s t k) (0, 0))

/-- The element run: the entries of the extended array from `auL p α` on, in order. -/
def auElems (p α s : ℕ) (u : List (ℤ × ℤ)) : List Val :=
  ((auExt p α s u).drop (auL p α)).map cfxVal

/-- The chunk of round `k` in the loop's encoding. -/
def auChunkF (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : Val :=
  .cons (ofList (auWts p α s t k)) (ofList (auWinV p α s t u k))

/-! ## Basic identities -/

theorem auChunkF_eq (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) :
    auChunkF p α s t u k = auChunk p α s t u k := rfl

theorem auWinV_length (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) :
    (auWinV p α s t u k).length = auL p α := by
  simp [auWinV, auWin]

theorem auWts_length (p α s t k : ℕ) : (auWts p α s t k).length = auL p α := by
  simp [auWts]

/-- `auElem` in the index order used by the window recurrence `auWinRec`. -/
theorem auElem_eq (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) :
    auElem p α s t u k = cfxVal ((auExt p α s u).getD (auK s t k + auL p α) (0, 0)) := by
  rw [auElem]
  exact congrArg (fun i => cfxVal ((auExt p α s u).getD i (0, 0)))
    (Eq.symm (Nat.add_comm (auK s t k) (auL p α)))

end Work.Resample
