import Mathlib
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx

/-!
# Flattening the slice-major listing (`HvdH.slices`)

`HvdH.slices A m B es` cuts a flat `A × m × B` array into its `A*B` slices of length `m`, slice
`s = a*B + b` being `j ↦ es[(a*m + j)*B + b]`.  Concatenating the slices lists the elements in
slice-major order, which is exactly the order of the labels `invIdx1 m B t` for `t = 0, …, A*m*B-1`.

Assuming `es.length = A*m*B`, the resulting list only ever reads in-range entries of `es`, so the
`Inhabited` default used inside `slices` can be replaced by any value (here `Val.nil`).
-/

namespace Work.SB.Core

/-- `List.range` splits at `a`: mapping `f` over `range (a+b)` is mapping `f` over `range a`
followed by `j ↦ f (a+j)` over `range b`. -/
lemma slicesFlatten_rangeShift {α : Type} (a b : ℕ) (f : ℕ → α) :
    (List.range a).map f ++ (List.range b).map (fun j => f (a + j))
      = (List.range (a + b)).map f := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- Flattening a `N × m` block matrix indexed by `(s,j) ↦ f (s*m+j)` enumerates `f` in order. -/
lemma slicesFlatten_rangeRangeMap {α : Type} (N m : ℕ) (f : ℕ → α) :
    ((List.range N).map (fun s => (List.range m).map (fun j => f (s * m + j)))).flatten
      = (List.range (N * m)).map f := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.map_singleton,
      List.flatten_singleton]
    show (List.range (N * m)).map f ++ (List.range m).map (fun j => f (N * m + j))
        = (List.range (N.succ * m)).map f
    rw [slicesFlatten_rangeShift, Nat.succ_mul]

theorem slicesFlattenEq (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) (es : List HvdH.Val)
    (hlen : es.length = A * m * B) :
    (HvdH.slices A m B es).flatten
      = (List.range (A * m * B)).map (fun t => es.getD (Work.Layout.invIdx1 m B t) HvdH.Val.nil) := by
  -- Rewrite the index `(s / B * m + j) * B + s % B` used by `slices` as `invIdx1 m B (s*m + j)`.
  have hstep : HvdH.slices A m B es
      = (List.range (A * B)).map (fun s => (List.range m).map
          (fun j => (fun t => es.getD (Work.Layout.invIdx1 m B t) (default : HvdH.Val)) (s * m + j))) := by
    unfold HvdH.slices
    apply List.map_congr_left
    intro s hs
    apply List.map_congr_left
    intro j hj
    show es.getD ((s / B * m + j) * B + s % B) (default : HvdH.Val)
        = es.getD (Work.Layout.invIdx1 m B (s * m + j)) (default : HvdH.Val)
    rw [Work.Layout.invIdx1_slice m B hm s j (List.mem_range.mp hj)]
  rw [hstep]
  -- Flatten the block matrix: the `k`-th entry is read at flat index `invIdx1 m B k`.
  rw [slicesFlatten_rangeRangeMap (A * B) m
    (fun t => es.getD (Work.Layout.invIdx1 m B t) (default : HvdH.Val))]
  rw [show A * B * m = A * m * B by ring]
  -- All indices are in range because `es.length = A*m*B`, so the two defaults agree.
  apply List.map_congr_left
  intro t ht
  have ht' : t < A * m * B := List.mem_range.mp ht
  have hidx : Work.Layout.invIdx1 m B t < es.length := by
    rw [hlen]
    exact Work.Layout.invIdx1_lt A m B hm hB t ht'
  rw [List.getD_eq_getElem es (default : HvdH.Val) hidx,
    List.getD_eq_getElem es HvdH.Val.nil hidx]

end Work.SB.Core
