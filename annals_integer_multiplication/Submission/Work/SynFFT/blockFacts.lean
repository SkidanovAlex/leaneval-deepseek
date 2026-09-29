import Mathlib
import Submission.Work.SynFFT.axisKit

/-!
# Pure list facts about the axis (block/row) decomposition

`blocksOf A t B es` cuts the flat array `es` into `A` consecutive blocks of `t*B` elements and
`rowsOf t B blk` cuts a block into `t` consecutive rows of `B` elements (`axisKit.lean`).  This
file collects the arithmetic/list facts used by the transpose assembly:

* `blocksOf` has length `A`, its members have length `t*B` (when `es` is long enough) and it
  coincides with the generic cut-out `chunkList (t*B)`;
* `rowsOf` has length `t`, its members have length `B`, and reading a position inside a row is
  reading the corresponding position of the flat block;
* the elementary window extractor `((xs.drop k).take n).getD i d = xs.getD (k + i) d` for `i < n`.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- Reading inside the window `(xs.drop k).take n` at an index `i < n` is reading `xs` at `k + i`
(an out-of-range read yields the default on both sides). -/
theorem getD_drop_take_eq {α : Type*} (xs : List α) (k n i : ℕ) (d : α) (h : i < n) :
    ((xs.drop k).take n).getD i d = xs.getD (k + i) d := by
  by_cases hlt : k + i < xs.length
  · have h1 : i < ((xs.drop k).take n).length := by
      rw [List.length_take, List.length_drop]; omega
    have h2 : i < (xs.drop k).length := by rw [List.length_drop]; omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hlt]
    rw [List.getElem_take (h := h1), List.getElem_drop (h := h2)]
  · have h1 : ((xs.drop k).take n).length ≤ i := by
      rw [List.length_take, List.length_drop]; omega
    have h2 : xs.length ≤ k + i := by omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

/-- `blocksOf` has exactly `A` entries. -/
theorem blocksOf_length (A t B : ℕ) (es : List HvdH.Val) : (blocksOf A t B es).length = A := by
  simp [blocksOf]

/-- The `a`-th block, as a literal window of `es`, for `a < A`. -/
theorem blocksOf_getD (A t B : ℕ) (es : List HvdH.Val) {a : ℕ} (ha : a < A) :
    (blocksOf A t B es).getD a [] = (es.drop (a * (t * B))).take (t * B) := by
  unfold blocksOf
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]
  rw [List.getElem_map, List.getElem_range]

/-- Every block of an `A*t*B`-long array has length `t*B`. -/
theorem blocksOf_mem_length (A t B : ℕ) (es : List HvdH.Val) (h : es.length = A * t * B)
    (_ht : 1 ≤ t) (_hB : 1 ≤ B) : ∀ blk ∈ blocksOf A t B es, blk.length = t * B := by
  intro blk hblk
  simp only [blocksOf, List.mem_map, List.mem_range] at hblk
  obtain ⟨a, ha, rfl⟩ := hblk
  rw [List.length_take, List.length_drop, h]
  have h2 : a * (t * B) + t * B ≤ A * t * B := by
    calc a * (t * B) + t * B = (a + 1) * (t * B) := by ring
      _ ≤ A * (t * B) := Nat.mul_le_mul_right _ (by omega)
      _ = A * t * B := by ring
  rw [Nat.min_eq_left (by omega)]

/-- `chunkList` with chunk size `t*B` is `blocksOf A t B` on an `A*t*B`-long array. -/
theorem chunkList_eq_blocksOf (A t B : ℕ) (es : List HvdH.Val) (h : es.length = A * t * B)
    (ht : 1 ≤ t) (hB : 1 ≤ B) : chunkList (t * B) es = blocksOf A t B es := by
  have hpos : 0 < t * B := by positivity
  unfold chunkList blocksOf
  have hdiv : es.length / (t * B) = A := by
    rw [h, Nat.mul_assoc]
    exact Nat.mul_div_cancel A hpos
  rw [hdiv]

/-- `rowsOf` has exactly `t` entries. -/
theorem rowsOf_length (t B : ℕ) (blk : List HvdH.Val) : (rowsOf t B blk).length = t := by
  simp [rowsOf]

/-- The `j`-th row, as a literal window of `blk`, for `j < t`. -/
theorem rowsOf_getD (t B : ℕ) (blk : List HvdH.Val) {j : ℕ} (hj : j < t) :
    (rowsOf t B blk).getD j [] = (blk.drop (j * B)).take B := by
  unfold rowsOf
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  rw [List.getElem_map, List.getElem_range]

/-- Every row of a `t*B`-long block has length `B`. -/
theorem rowsOf_getD_length (t B : ℕ) (blk : List HvdH.Val) (h : blk.length = t * B) :
    ∀ j < t, ((rowsOf t B blk).getD j []).length = B := by
  intro j hj
  rw [rowsOf_getD t B blk hj, List.length_take, List.length_drop, h]
  have h2 : j * B + B ≤ t * B := by
    calc j * B + B = (j + 1) * B := by ring
      _ ≤ t * B := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.min_eq_left (by omega)]

/-- Reading the `b`-th entry of the `j`-th row of a `t*B`-long block is reading the flat block at
`j*B + b`. -/
theorem rowsOf_getD_getD (t B : ℕ) (blk : List HvdH.Val) (_h : blk.length = t * B) :
    ∀ j < t, ∀ b < B, ((rowsOf t B blk).getD j []).getD b HvdH.Val.nil =
      blk.getD (j * B + b) HvdH.Val.nil := by
  intro j hj b hb
  rw [rowsOf_getD t B blk hj]
  exact getD_drop_take_eq blk (j * B) B b HvdH.Val.nil hb

theorem blockFacts :
    (∀ (A t B : ℕ) (es : List HvdH.Val), (blocksOf A t B es).length = A) ∧
    (∀ (A t B : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      ∀ blk ∈ blocksOf A t B es, blk.length = t * B) ∧
    (∀ (A t B : ℕ) (es : List HvdH.Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      chunkList (t * B) es = blocksOf A t B es) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), (rowsOf t B blk).length = t) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → ∀ j < t,
      ((rowsOf t B blk).getD j []).length = B) ∧
    (∀ (xs : List HvdH.Val) (k n i : ℕ) (d : HvdH.Val), i < n →
      ((xs.drop k).take n).getD i d = xs.getD (k + i) d) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → ∀ j < t, ∀ b < B,
      ((rowsOf t B blk).getD j []).getD b HvdH.Val.nil = blk.getD (j * B + b) HvdH.Val.nil) :=
  ⟨blocksOf_length,
   fun A t B es h ht hB => blocksOf_mem_length A t B es h ht hB,
   fun A t B es h ht hB => chunkList_eq_blocksOf A t B es h ht hB,
   rowsOf_length,
   fun t B blk h => rowsOf_getD_length t B blk h,
   fun xs k n i d h => getD_drop_take_eq xs k n i d h,
   fun t B blk h => rowsOf_getD_getD t B blk h⟩

end Work.SynFFT
