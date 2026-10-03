/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Bookkeeping for the up-block descent

This file provides the index-level vocabulary of the *up-block descent* of
`Submission/Work/OROneRel/NOTES_twoLetter_hnnConjMap_routes.md`, §10.3:

Given a function `f : Fin n → α` on a block of `n` letters and an index `m` (the *first return to
the base level*), the sub-block `[1, m-1]` is re-indexed by `Fin (m - 1)` via `subIdx`, and the
tail `[m, n-1]` by `Fin (n - m)` via `tailIdx`.  `IsPeak` records the "clamped" peak condition:
the level just before `i` (read as `b - 1` at the left end) equals the level just after `i` (read as
`b - 1` at the right end).
-/
import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.tlBandDescent

namespace Work.OROneRel

/-- The index `0` of `Fin n`. -/
def idx0 {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨0, hn⟩

/-- The predecessor index of `i : Fin n`. -/
def predIdx {n : ℕ} (hn : 1 ≤ n) (i : Fin n) : Fin n :=
  ⟨i.1 - 1, fin_sub_one_lt hn i⟩

/-- **The peak condition** at index `i` of a block with base level `b`: the level just before `i`
(read as `b - 1` when `i` is the first index of the block) equals the level just after `i` (read as
`b - 1` when `i` is the last index of the block). -/
def IsPeak (b : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (i : Fin n) : Prop :=
  (if i = idx0 hn then b - 1 else t (predIdx hn i)) =
    (if h : i.1 + 1 < n then t ⟨i.1 + 1, h⟩ else b - 1)

/-- The index `j ↦ j + 1` of `Fin (m - 1)` inside `Fin n`, for `m ≤ n`: the sub-block `[1, m-1]`. -/
def subIdx {n : ℕ} {m : ℕ} (hm : m ≤ n) (j : Fin (m - 1)) : Fin n :=
  ⟨j.1 + 1, by omega⟩

/-- The index `j ↦ m + j` of `Fin (n - m)` inside `Fin n`: the tail `[m, n-1]`. -/
def tailIdx {n : ℕ} {m : ℕ} (j : Fin (n - m)) : Fin n :=
  ⟨m + j.1, by omega⟩

/-- Re-indexing of the sub-block `[1, m-1]` of `f : Fin n → α`. -/
def subF {α : Type*} {n : ℕ} (f : Fin n → α) (m : ℕ) (hm : m ≤ n) : Fin (m - 1) → α :=
  fun j => f (subIdx hm j)

/-- Re-indexing of the tail `[m, n-1]` of `f : Fin n → α`. -/
def tailF {α : Type*} {n : ℕ} (f : Fin n → α) (m : ℕ) : Fin (n - m) → α :=
  fun j => f (tailIdx j)

/-- `1 ≤ m - 1` for `2 ≤ m`. -/
theorem one_le_sub_one {m : ℕ} (hm2 : 2 ≤ m) : 1 ≤ m - 1 := by omega

@[simp] theorem subF_apply {α : Type*} {n : ℕ} (f : Fin n → α) (m : ℕ) (hm : m ≤ n)
    (j : Fin (m - 1)) : subF f m hm j = f (subIdx hm j) := rfl

@[simp] theorem tailF_apply {α : Type*} {n : ℕ} (f : Fin n → α) (m : ℕ)
    (j : Fin (n - m)) : tailF f m j = f (tailIdx j) := rfl

@[simp] theorem subIdx_val {n : ℕ} {m : ℕ} (hm : m ≤ n) (j : Fin (m - 1)) :
    (subIdx hm j).1 = j.1 + 1 := rfl

@[simp] theorem tailIdx_val {n : ℕ} {m : ℕ} (j : Fin (n - m)) : (tailIdx j).1 = m + j.1 := rfl

end Work.OROneRel
