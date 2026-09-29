import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.encodeNatBits

/-!
# Shared definitions for `Work.Transform.phiChunkWord` (paper Prop 3.5, chunking phase)

The chunking phase of the paper's `T̃` cuts the flat vector `cvecVal x` (length `M * r`) into
`M` consecutive blocks of length `r`.  Two auxiliary objects describe this:

* `chunkArr M r x`: the list of the `M` blocks `i ↦ (x.drop (i * r)).take r`;
* `chunkVals r x`: the list of values `LayoutLib.chunksOf r` hands to `ofList` when it is applied
  to `cvecVal x`, i.e. `i ↦ ofList (((x.map cfxVal).drop (i * r)).take r)`.

`ofList_chunkVals` (`Submission/Work/Transform/chunkValsOfList.lean`) identifies
`ofList (chunkVals r x)` with `rarrVal (chunkArr M r x)`; `chunkArrFacts`
(`Submission/Work/Transform/chunkArrFacts.lean`) collects the size/index facts about `chunkArr`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- The `M` consecutive chunks of length `r` of a list `w` of length `M * r`: the `i`-th chunk is
`(w.drop (i * r)).take r`.  The `R`-array of these chunks is what `phiChunkWord` produces. -/
def chunkArr (M r : ℕ) (w : List (ℤ × ℤ)) : List (List (ℤ × ℤ)) :=
  (List.range M).map (fun i => (w.drop (i * r)).take r)

/-- The value list that `LayoutLib.chunksOf r` builds when applied to `cvecVal w`
(`cvecVal w = ofList (w.map cfxVal)`): `i ↦ ofList ((w.map cfxVal).drop (i * r) |>.take r)`. -/
def chunkVals (r : ℕ) (w : List (ℤ × ℤ)) : List Val :=
  (List.range ((w.map cfxVal).length / r)).map
    (fun i => ofList (((w.map cfxVal).drop (i * r)).take r))

/-! ## Indexing helpers -/

/-- The `i`-th entry of `(List.range M).map f`, for `i < M` (independent of the default). -/
theorem range_map_getD {α : Type} (f : ℕ → α) (d : α) {M i : ℕ} (hi : i < M) :
    ((List.range M).map f).getD i d = f i := by
  rw [List.getD_eq_getElem (n := i) _ _ (by simpa using hi),
    List.getElem_map, List.getElem_range (by simpa using hi)]

theorem chunkArr_length (M r : ℕ) (w : List (ℤ × ℤ)) : (chunkArr M r w).length = M := by
  simp [chunkArr]

theorem chunkArr_getD {M r : ℕ} {w : List (ℤ × ℤ)} {i : ℕ} (hi : i < M) :
    (chunkArr M r w).getD i [] = (w.drop (i * r)).take r := by
  rw [chunkArr, range_map_getD _ _ hi]

end Work.Transform
