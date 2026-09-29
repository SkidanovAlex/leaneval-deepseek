import Mathlib
import Submission.Work.Resample.auDefs

/-!
# Definitions for the resampling word `q` of Lemma 4.9 (`Work.Resample.auConv`)

This module fixes the data the uniform resampling word manipulates.  Nothing here is a
program; the words themselves are stated in `Submission/Work/Resample/auConv.lean` (assembly)
and in the sibling files `auSetup`, `auChunk` (delegated pieces).

* `auExt p α s u` is the extended input array: `auCop p α s` copies of `u`, dropped so that
  index `0` corresponds to the global index `auOff p α s`; thus its entry `auK s t k + i`
  is the input entry `u (auJ p α s t k i)` (see `Work.Resample.auIdx`).
* `auWin p α s t u k` is the window of output `k`: the `auL p α` consecutive entries of the
  extended array starting at `auK s t k`.
* `auWts p α s t k` is the weight list of output `k` (the `auL p α` integers `auWt …`), and
  `auChunk p α s t u k = cons (ofList (auWts …)) (ofList (auWin … ·))` packages the window
  together with its weights: this is the `k`-th element of the stream over which the main
  word maps.
* `auStream p α s t u` is that stream (a single `Val`, a list of chunks).

The map word itself only ever sees one chunk at a time; the invariants it needs are stated in
`Work.Resample.auChunk`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The extended input array: `auCop p α s` copies of `u` (as a flat list), dropped by `auOff`.
Index `ℓ` of this list corresponds to the global index `auOff p α s + ℓ`. -/
def auExt (p α s : ℕ) (u : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  ((List.replicate (auCop p α s) u).flatten).drop (auOff p α s)

/-- The window of output `k`: the `auL p α` entries of the extended array from `auK s t k` on. -/
def auWin (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : List (ℤ × ℤ) :=
  (List.range (auL p α)).map fun i => (auExt p α s u).getD (auK s t k + i) (0, 0)

/-- The weight list of output `k`, as a list of integer values. -/
def auWts (p α s t k : ℕ) : List Val :=
  (List.range (auL p α)).map fun i => Val.int (auWt p α t (auNsq p α s t k i))

/-- The `k`-th chunk: its weight list paired with its window (as values). -/
def auChunk (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ) : Val :=
  .cons (ofList (auWts p α s t k)) (ofList ((auWin p α s t u k).map cfxVal))

/-- The stream over which the resampling word maps: the list of all chunks. -/
def auStream (p α s t : ℕ) (u : List (ℤ × ℤ)) : List Val :=
  (List.range t).map fun k => auChunk p α s t u k

/-- The stream as a single value. -/
def auStreamV (p α s t : ℕ) (u : List (ℤ × ℤ)) : Val := ofList (auStream p α s t u)

end Work.Resample
