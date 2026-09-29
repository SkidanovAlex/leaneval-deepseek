import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# SynFFT: shared definitions for the interleave ("merge") pass assembly

The pass word (`HasMrgPass`) is `chunksOf (2s)` + `KLib.mapList` of the block word (`HasMrgBlk`)
+ `flatten`.  This module fixes the objects appearing in that assembly:

* `blkVec s ws b` — the `b`-th block of `2s` coefficient vectors of `ws`;
* `vecFun p r v` — the *exact* target function of a list `v` of coefficient vectors, i.e. the
  function `q c ↦ fxC p (v q c)`.  The block word is applied with this target and error `0`, so
  that the interleave (a pure permutation of the two halves) does not add any error;
* `blkPre`, `blkRel` — the predicate / binary relation handed to `KLib.mapList`;
* `chunkVals_xmrgPassDefs s ws` — the list of chunk values produced by `LayoutLib.chunksOf`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH
open Classical

/-- The `b`-th block of `2 * s` coefficient vectors of `ws`. -/
def blkVec (s : ℕ) (ws : List (List (ℤ × ℤ))) (b : ℕ) : List (List (ℤ × ℤ)) :=
  (ws.drop (b * (2 * s))).take (2 * s)

/-- The exact target function of the list `v` of coefficient vectors: `q c ↦ fxC p (v q c)`. -/
noncomputable def vecFun (p r : ℕ) (v : List (List (ℤ × ℤ))) : Arr r :=
  fun q c =>
    let z : ℤ × ℤ := ((v.getD q []).getD (c : ℕ) (0, 0))
    fxC p z

/-- The precondition of `KLib.mapList`: `x` is a block value of `2 * s` in-disc vectors. -/
def blkPre (p r s : ℕ) (x : Val) : Prop :=
  ∃ v : List (List (ℤ × ℤ)), x = ofList (cvecs v) ∧ v.length = 2 * s ∧
    (∀ w ∈ v, InDiscVec p r w)

/-- The relation of `KLib.mapList`: `y` is the (uniquely determined) block output for `x`, and
it approximates `mrgN r s` of the *exact* target function of the input vectors with error `0`. -/
def blkRel (p r s : ℕ) (x y : Val) : Prop :=
  ∃ v v' : List (List (ℤ × ℤ)), x = ofList (cvecs v) ∧ y = ofList (cvecs v') ∧
    v.length = 2 * s ∧ v'.length = 2 * s ∧ (∀ w ∈ v', InDiscVec p r w) ∧
    ApproxSL p r (2 * s) v' (mrgN r s (vecFun p r v)) 0

/-- The list of chunk values produced by `LayoutLib.chunksOf` with `m = 2 * s` on `cvecs ws`. -/
def chunkVals_xmrgPassDefs (s : ℕ) (ws : List (List (ℤ × ℤ))) : List Val :=
  (List.range (ws.length / (2 * s))).map (fun b => ofList (cvecs (blkVec s ws b)))

/-- Extraction of the block output vectors from a list `ys` of block values: `extractV ... ys b`
is the vector list whose `ofList`-value is `ys.getD b .nil`, provided such a list exists; it is
`[]` otherwise.  `extractV_spec` below is the only property used. -/
noncomputable def extractV (p r s : ℕ) (ws : List (List (ℤ × ℤ))) (ys : List Val) (b : ℕ) :
    List (List (ℤ × ℤ)) :=
  if h : ∃ v' : List (List (ℤ × ℤ)), ys.getD b .nil = ofList (cvecs v') ∧ v'.length = 2 * s ∧
      (∀ w ∈ v', InDiscVec p r w) ∧
      ApproxSL p r (2 * s) v' (mrgN r s (vecFun p r (blkVec s ws b))) 0
  then Classical.choose h else []

/-- The specification of `extractV`. -/
theorem extractV_spec (p r s : ℕ) (ws : List (List (ℤ × ℤ))) (ys : List Val) (b : ℕ)
    (h : ∃ v' : List (List (ℤ × ℤ)), ys.getD b .nil = ofList (cvecs v') ∧ v'.length = 2 * s ∧
      (∀ w ∈ v', InDiscVec p r w) ∧
      ApproxSL p r (2 * s) v' (mrgN r s (vecFun p r (blkVec s ws b))) 0) :
    ys.getD b .nil = ofList (cvecs (extractV p r s ws ys b)) ∧
    (extractV p r s ws ys b).length = 2 * s ∧
    (∀ w ∈ extractV p r s ws ys b, InDiscVec p r w) ∧
    ApproxSL p r (2 * s) (extractV p r s ws ys b)
      (mrgN r s (vecFun p r (blkVec s ws b))) 0 := by
  rw [extractV, dif_pos h]
  exact Classical.choose_spec h

end Work.SynFFT
