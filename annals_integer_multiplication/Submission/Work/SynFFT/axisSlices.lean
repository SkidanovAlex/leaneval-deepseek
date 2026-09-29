import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.colsTranspose
import Submission.Work.SynFFT.blockFacts
import Submission.Work.SynFFT.slicesCanon

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-!
# The pure list content of the axis (gather) step: `Work.SynFFT.axisSlices`

`HvdH.slices A t B es` is the flat `A × t × B` array `es` regrouped into its `A*B` slices of
length `t` (slice `a*B + b` is `j ↦ es[(a*t+j)*B + b]`).  `axisSlices` collects the list facts
about this regrouping and about the block/row/column decomposition used by the transpose word
(`axisKit.lean`):

* the `A` blocks `blocksOf A t B es` of `t*B` consecutive elements, the agreement with the generic
  cut-out `chunkList (t*B)`, and the row decomposition `rowsOf t B blk` of a block;
* the columns `cols (rowsOf t B blk)` of a block, and the identification of the flattening of
  `HvdH.slices` with the flattening of the columns of the blocks (`slices_connection`).

The three mathematical ingredients are the delegated lemmas `colTranspose`/`colsTranspose`
(transpose of equal-length rows), `blockFacts` (window arithmetic of `blocksOf`/`rowsOf`) and
`slicesCanon` (`HvdH.slices` as a triple range/map).  The only work left here is the assembly.
-/

/-- `getD` of a `List.map` over `List.range`: the entry at `j < n` is `f j`. -/
theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

/-- `(l.take n).length = n` when `n` does not exceed the length of `l`. -/
theorem length_take_ax {α : Type} (l : List α) (n : ℕ) (h : n ≤ l.length) :
    (l.take n).length = n := by
  rw [List.length_take, Nat.min_eq_left h]

theorem axisSlices :
    (∀ (A t B : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (blocksOf A t B es).length = A) ∧
    (∀ (A t B : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      ∀ blk ∈ blocksOf A t B es, blk.length = t * B) ∧
    (∀ (A t B : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      chunkList (t * B) es = blocksOf A t B es) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → (rowsOf t B blk).length = t) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → ∀ j < t,
      ((rowsOf t B blk).getD j []).length = B) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → 1 ≤ t → 1 ≤ B → ∀ b < B,
      (cols (rowsOf t B blk)).getD b [] =
        (List.range t).map (fun j => blk.getD (j * B + b) HvdH.Val.nil)) ∧
    (∀ (A t B : ℕ) (es : List HvdH.Val), 1 ≤ A → 1 ≤ t → 1 ≤ B → es.length = A * t * B →
      List.flatten (HvdH.slices A t B es) =
        ((blocksOf A t B es).map (fun blk => (cols (rowsOf t B blk)).flatten)).flatten) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A t B es h ht hB
    exact blockFacts.1 A t B es
  · intro A t B es h ht hB
    exact blockFacts.2.1 A t B es h ht hB
  · intro A t B es h ht hB
    exact blockFacts.2.2.1 A t B es h ht hB
  · intro t B blk h
    exact blockFacts.2.2.2.1 t B blk
  · intro t B blk h j hj
    exact blockFacts.2.2.2.2.1 t B blk h j hj
  · intro t B blk hlen ht hB b hb
    -- every row of `blk` has length `B`
    have hrowslen : ∀ s ∈ rowsOf t B blk, s.length = B := by
      intro s hs
      simp only [rowsOf, List.mem_map, List.mem_range] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      rw [length_take_ax]
      rw [List.length_drop, hlen]
      have h2 : j * B + B ≤ t * B := by
        have h3 : (j + 1) * B ≤ t * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj)
        rwa [Nat.succ_mul] at h3
      omega
    have hne : rowsOf t B blk ≠ [] := by
      rw [List.ne_nil_iff_length_pos, blockFacts.2.2.2.1 t B blk]
      omega
    -- the `b`-th column is the `map` of the rows at position `b`
    rw [colsTranspose (rowsOf t B blk) B hne hrowslen]
    rw [getD_range_map (fun b' => (rowsOf t B blk).map (fun s => s.getD b' HvdH.Val.nil)) [] hb]
    show (rowsOf t B blk).map (fun s => s.getD b HvdH.Val.nil) =
      (List.range t).map (fun j => blk.getD (j * B + b) HvdH.Val.nil)
    -- rewrite both sides as `map`s over `List.range t`
    simp only [rowsOf]
    rw [List.map_map]
    show (List.range t).map (fun j => ((blk.drop (j * B)).take B).getD b HvdH.Val.nil) =
      (List.range t).map (fun j => blk.getD (j * B + b) HvdH.Val.nil)
    refine List.map_congr_left (fun j hj => ?_)
    have hj' : j < t := List.mem_range.mp hj
    -- the `j`-th row is `(blk.drop (j*B)).take B`, and reading its `b`-th entry is reading `blk`
    have hc7 := blockFacts.2.2.2.2.2.2 t B blk hlen j hj' b hb
    have hrow : (rowsOf t B blk).getD j [] = (blk.drop (j * B)).take B := by
      simp only [rowsOf]
      exact getD_range_map (fun j' => (blk.drop (j' * B)).take B) [] hj'
    rw [hrow] at hc7
    exact hc7
  · intro A t B es hA ht hB hlen
    -- per block: the columns of its rows are the slices of that block
    have hblk : ∀ a ∈ List.range A,
        (cols (rowsOf t B ((es.drop (a * (t * B))).take (t * B)))).flatten =
        ((List.range B).map (fun b => (List.range t).map (fun j =>
          es.getD ((a * t + j) * B + b) HvdH.Val.nil))).flatten := by
      intro a ha
      have ha' : a < A := List.mem_range.mp ha
      -- the block `a` has length `t*B`
      have hlen_a : ((es.drop (a * (t * B))).take (t * B)).length = t * B := by
        rw [length_take_ax]
        rw [List.length_drop]
        have h3 : (a + 1) * (t * B) ≤ es.length := by
          rw [hlen]
          calc (a + 1) * (t * B) ≤ A * (t * B) :=
                Nat.mul_le_mul_right (t * B) (Nat.succ_le_of_lt ha')
            _ = A * t * B := by ring
        have h4 : a * (t * B) + t * B ≤ es.length := by rwa [Nat.succ_mul] at h3
        omega
      -- every row of the block has length `B`
      have hrowslen_a : ∀ s ∈ rowsOf t B ((es.drop (a * (t * B))).take (t * B)), s.length = B := by
        intro s hs
        simp only [rowsOf, List.mem_map, List.mem_range] at hs
        obtain ⟨j, hj, rfl⟩ := hs
        rw [length_take_ax]
        rw [List.length_drop, hlen_a]
        have h2 : j * B + B ≤ t * B := by
          have h3 : (j + 1) * B ≤ t * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj)
          rwa [Nat.succ_mul] at h3
        omega
      have hne_a : rowsOf t B ((es.drop (a * (t * B))).take (t * B)) ≠ [] := by
        rw [List.ne_nil_iff_length_pos,
          blockFacts.2.2.2.1 t B ((es.drop (a * (t * B))).take (t * B))]
        omega
      rw [colsTranspose _ B hne_a hrowslen_a]
      apply congrArg List.flatten
      refine List.map_congr_left (fun b hb => ?_)
      have hb' : b < B := List.mem_range.mp hb
      show (rowsOf t B ((es.drop (a * (t * B))).take (t * B))).map
            (fun s => s.getD b HvdH.Val.nil) =
          (List.range t).map (fun j => es.getD ((a * t + j) * B + b) HvdH.Val.nil)
      simp only [rowsOf]
      rw [List.map_map]
      show (List.range t).map (fun j =>
          (((es.drop (a * (t * B))).take (t * B)).drop (j * B)).take B |>.getD b HvdH.Val.nil) =
        (List.range t).map (fun j => es.getD ((a * t + j) * B + b) HvdH.Val.nil)
      refine List.map_congr_left (fun j hj => ?_)
      have hj' : j < t := List.mem_range.mp hj
      have hbnd : j * B + B ≤ t * B := by
        have h3 : (j + 1) * B ≤ t * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj')
        rwa [Nat.succ_mul] at h3
      have hc7 := blockFacts.2.2.2.2.2.2 t B ((es.drop (a * (t * B))).take (t * B)) hlen_a j hj' b hb'
      have hrow : (rowsOf t B ((es.drop (a * (t * B))).take (t * B))).getD j [] =
          (((es.drop (a * (t * B))).take (t * B)).drop (j * B)).take B := by
        simp only [rowsOf]
        exact getD_range_map
          (fun j' => (((es.drop (a * (t * B))).take (t * B)).drop (j' * B)).take B) [] hj'
      rw [hrow] at hc7
      rw [hc7]
      -- read the entry of the block as the corresponding entry of the flat array
      rw [blockFacts.2.2.2.2.2.1 es (a * (t * B)) (t * B) (j * B + b) HvdH.Val.nil (by omega)]
      exact congrArg (fun i => es.getD i HvdH.Val.nil) (by ring)
    rw [slicesCanon A t B es HvdH.Val.nil hlen]
    unfold blocksOf
    rw [List.map_map]
    apply congrArg List.flatten
    exact List.map_congr_left (fun a ha => (hblk a ha).symm)

end Work.SynFFT
