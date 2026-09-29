import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auWinSlice

namespace Work.Resample

open HvdH

/-!
# Indexing the element run `auElems` (paper Lemma 4.9, sliding window)

`auElems p α s u` is the extended input array `auExt p α s u`, dropped by the window length
`auL p α` and mapped to values through `cfxVal`: the run of entries that a pointer advancing on a
slide of `1` walks through.  Its `k`-th entry must therefore be the entry that the window of round
`k` acquires when its slide is `1`, namely `auElem p α s t u k`, provided the look-up is in range.

Both facts are pure `List` bookkeeping:

* `(l.drop n).map f` at index `k` looks up `l` at index `n + k` (`List.getElem?_map`,
  `List.getElem?_drop`),
* `l[n]? = some (l.getD n d)` as soon as `n < l.length` (`List.getD_eq_getElem`,
  `List.getElem?_eq_getElem`).

The hypothesis `h` is exactly the in-range condition `auL p α + auK s t k < (auExt p α s u).length`.
-/

/-- Pointwise form: the `k`-th entry of `(l.drop n).map f` is `f` applied to the `(n+k)`-th entry of
`l`, whenever the look-up is in range. -/
lemma auDropMap_getElem?_getD {β γ : Type*} (l : List β) (f : β → γ) (d : β) (n k : ℕ)
    (h : n + k < l.length) :
    ((l.drop n).map f)[k]? = some (f (l.getD (n + k) d)) := by
  rw [List.getElem?_map, List.getElem?_drop,
    List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem auElemsElem (p α s t : ℕ) (u : List (ℤ × ℤ)) (k : ℕ)
    (h : Work.Resample.auL p α + Work.Resample.auK s t k < (Work.Resample.auExt p α s u).length) :
    (Work.Resample.auElems p α s u)[Work.Resample.auK s t k]? =
      some (Work.Resample.auElem p α s t u k) := by
  rw [auElems, auElem]
  exact auDropMap_getElem?_getD (auExt p α s u) cfxVal (0, 0) (auL p α) (auK s t k) h

end Work.Resample
