import Mathlib
import Submission.Work.Transform.phiChunkDefs

/-!
# `ofList (chunkVals r w) = rarrVal (chunkArr M r w)`

The chunking phase of `phiChunkWord` (paper Prop 3.5) hands `LayoutLib.chunksOf r` the flat
vector `cvecVal w`; the value it returns is `ofList (chunkVals r w)`.  The intended result of
the phase is the `R`-array `rarrVal (chunkArr M r w)` of the consecutive length-`r` blocks of
`w`.  This file identifies the two.

The proof is purely combinatorial: `ofList` and `cvecVal` are iterated `cons`/`nil` constructors,
so it suffices to compare the two lists elementwise, where each element is the same length-`r`
block `(w.drop (i*r)).take r` of `w`, once mapped by `cfxVal` (using
`List.map_drop`/`List.map_take` to push the map inside the slice), and to note that
`(w.map cfxVal).length / r = M` since `w.length = M * r` and `1 ≤ r`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

theorem ofListChunkVals {M r : ℕ} {w : List (ℤ × ℤ)} (hw : w.length = M * r) (hr : 1 ≤ r) :
    HvdH.ofList (Work.Transform.chunkVals r w) =
      HvdH.rarrVal (Work.Transform.chunkArr M r w) := by
  have hr0 : 0 < r := hr
  rw [HvdH.rarrVal, Work.Transform.chunkArr, List.map_map, Work.Transform.chunkVals,
    List.length_map, hw, Nat.mul_div_left M hr0]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [← List.map_drop, ← List.map_take]
  rfl

end Work.Transform
