import Mathlib
import Submission.Work.SynFFT.axisKit

/-!
# Canonical form of `List.flatten (HvdH.slices A t B es)`

`HvdH.slices A t B es` cuts a flat `A × t × B` array into its `A*B` slices (slice `s = a*B + b`
is `j ↦ es[(a*t + j)*B + b]`).  Flattening the slices concatenates the slices in the order
`s = a*B + b`, i.e. it lists the entries in the order `(a, b, j)`.  Here we prove the
corresponding closed form, in which the flattened `getD`-read of a possibly out-of-range `es`
is compared against the same read with an arbitrary fallback `d`.

The proof splits the index range `[0, A*B)` into the `A` blocks `a ↦ [a*B, …, a*B + (B-1)]`
(`range_mul_eq_flatMap`), reads `s / B` and `s % B` on such a block, and uses that the
occurring indices are in range (`slicesIdx_canon_lt`) so that both fallback values are
irrelevant.
-/

namespace Work.SynFFT

open HvdH

/-- Flattening a mapped list is a `flatMap`: `(l.map f).flatten = l.flatMap f`. -/
theorem flatten_map_eq {α β : Type} (f : α → List β) (l : List α) :
    (l.map f).flatten = List.flatMap f l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- `List.range (A * B)` splits into the `A` consecutive blocks of `B` consecutive numbers,
block `a` being `a ↦ [a*B, …, a*B + (B-1)]`. -/
theorem range_mul_eq_flatMap (A B : ℕ) :
    List.range (A * B) =
      List.flatMap (fun a => (List.range B).map (fun b => a * B + b)) (List.range A) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- The index `(a*t + j)*B + b` (`a < A`, `b < B`, `j < t`) is a valid index of a flat
`A × t × B` array. -/
theorem slicesIdx_canon_lt (A t B a b j : ℕ) (ha : a < A) (hb : b < B) (hj : j < t) :
    (a * t + j) * B + b < A * t * B := by
  have hle : a * t + j + 1 ≤ A * t := by
    have h1 : a + 1 ≤ A := ha
    calc a * t + j + 1 ≤ a * t + t := by omega
      _ = (a + 1) * t := by ring
      _ ≤ A * t := Nat.mul_le_mul_right t h1
  calc (a * t + j) * B + b < (a * t + j) * B + B := by omega
    _ = (a * t + j + 1) * B := by ring
    _ ≤ A * t * B := Nat.mul_le_mul_right B hle

theorem slicesCanon (A t B : ℕ) (es : List HvdH.Val) (d : HvdH.Val)
    (h : es.length = A * t * B) :
    List.flatten (HvdH.slices A t B es) =
      ((List.range A).map (fun a => ((List.range B).map (fun b =>
        (List.range t).map (fun j => es.getD ((a * t + j) * B + b) d))).flatten)).flatten := by
  -- Rewrite both sides into `flatMap` form over `List.range A`.
  have hL : List.flatten (HvdH.slices A t B es)
      = List.flatMap (fun s => (List.range t).map (fun j =>
          es.getD ((s / B * t + j) * B + s % B) default)) (List.range (A * B)) := by
    rw [HvdH.slices]
    exact flatten_map_eq _ _
  have hR : ((List.range A).map (fun a => ((List.range B).map (fun b =>
        (List.range t).map (fun j => es.getD ((a * t + j) * B + b) d))).flatten)).flatten
      = List.flatMap (fun a => List.flatMap (fun b => (List.range t).map (fun j =>
          es.getD ((a * t + j) * B + b) d)) (List.range B)) (List.range A) := by
    rw [flatten_map_eq]
    apply List.flatMap_congr
    intro a _
    exact flatten_map_eq _ _
  rw [hL, hR, range_mul_eq_flatMap, List.flatMap_assoc]
  -- Both sides are now `flatMap` over `List.range A`; compare blockwise.
  apply List.flatMap_congr
  intro a ha
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro b hb
  rw [List.mem_range] at ha hb
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le b) hb
  have hdiv : (a * B + b) / B = a := by
    rw [Nat.mul_comm a B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hmod : (a * B + b) % B = b := by
    rw [Nat.mul_comm a B, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hidx : (a * t + j) * B + b < es.length := by
    rw [h]; exact slicesIdx_canon_lt A t B a b j ha hb hj
  rw [hdiv, hmod, List.getD_eq_getElem es default hidx, List.getD_eq_getElem es d hidx]

end Work.SynFFT
