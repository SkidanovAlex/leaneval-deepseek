import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx
import Submission.Work.SB.keyFacts
import Submission.Work.SB.Core.sortedLabelledEq
import Submission.Work.SB.Core.slicesFlattenEq
import Submission.Work.SB.chunksFlatten

/-!
# Facts about `HvdH.slices`

`HvdH.slices A m B es` cuts a flat `A × m × B` array into its `A*B` slices of length `m`
(slice `s = a*B + b` is `j ↦ es[(a*m + j)*B + b]`).

This file proves `Work.SB.slicesFacts`, the statement needed by the sort-based `applyAlong`
pipeline:
* the shape facts: `A*B` slices, each of length `m`, total flattened length `A*m*B`;
* the degenerate case `m = 0`: all slices are empty;
* the flattening is the concatenation of the slices (inverse of `flatten`);
* the main point: a list of `pairKey`-sorted labelled records which is a permutation of the
  `keyIdx1 m B`-labelled `es` strips to the flattened slices
  (`Work.SB.Core.sortedLabelledEq` + `Work.SB.Core.slicesFlattenEq`).
-/

namespace Work.SB

open HvdH
open Work.Layout

/-- Every element of `slices A m B es` has length `m`. -/
private lemma slices_mem_length (A m B : ℕ) (es : List Val) :
    ∀ l ∈ slices A m B es, l.length = m := by
  intro l hl
  rw [HvdH.slices] at hl
  obtain ⟨s, _hs, rfl⟩ := List.mem_map.mp hl
  simp

theorem slicesFacts (A m B : ℕ) (es : List Val) :
    (slices A m B es).length = A * B ∧
    (∀ s, s < A * B → ((slices A m B es).getD s []).length = m) ∧
    (slices A m B es).flatten.length = A * m * B ∧
    slices A 0 B es = List.replicate (A * B) [] ∧
    (∀ (_hm : 0 < m), (List.range ((slices A m B es).flatten.length / m)).map
        (fun i => ((slices A m B es).flatten.drop (i * m)).take m) = slices A m B es) ∧
    (∀ (_hm : 0 < m) (_hB : 0 < B) (hlen : es.length = A * m * B) (ys : List Val),
      ys.Perm ((List.range (A * m * B)).map
        (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) →
      ys.Pairwise (fun a b => pairKey a < pairKey b) → ys.map unlab = (slices A m B es).flatten) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- shape: `A * B` slices
    simp [HvdH.slices]
  · -- each slice has length `m`
    intro s hs
    rw [HvdH.slices]
    rw [List.getD_eq_getElem _ _ (by simpa using hs)]
    simp
  · -- total flattened length `A * m * B`
    rw [HvdH.slices, List.length_flatten, List.map_map]
    have hconst : (List.map (List.length ∘ fun s =>
          List.map (fun j => es.getD ((s / B * m + j) * B + s % B) default) (List.range m))
          (List.range (A * B))).sum = A * B * m := by
      have hmap : List.map (List.length ∘ fun s =>
            List.map (fun j => es.getD ((s / B * m + j) * B + s % B) default) (List.range m))
            (List.range (A * B)) = List.replicate (A * B) m := by
        simp [Function.comp_def]
      rw [hmap, List.sum_const_nat]
    rw [hconst]; ring
  · -- the degenerate case `m = 0`
    simp [HvdH.slices]
  · -- chunks of the flattened list are the slices
    intro hm
    exact chunksFlatten (slices A m B es) m hm (slices_mem_length A m B es)
  · -- the sorted labelled list strips to the flattened slices
    intro hm hB hlen ys hperm hsort
    have h1 := Core.sortedLabelledEq A m B hm hB es ys hlen hperm hsort
    have h2 := Core.slicesFlattenEq A m B hm hB es hlen
    rw [h1, h2, List.map_map]
    rfl

end Work.SB
