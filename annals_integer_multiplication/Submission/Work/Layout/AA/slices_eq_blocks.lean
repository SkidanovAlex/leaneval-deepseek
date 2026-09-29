import Mathlib
import Submission.Work.Layout.AA.PureDefs

/-!
# `slices` is the concatenation of the columns of the blocks

A flat `A × m × B` array `es` (element `(a,j,b)` at flat index `(a*m+j)*B + b`) has `A*B` slices of
length `m`, slice `a*B + b` being `j ↦ es[(a*m+j)*B + b]` (`HvdH.slices`).  Viewing `es` instead as
`A` blocks, each a flat `m × B` array, the columns of block `a` are exactly the slices
`a*B + b` (`b < B`) of that block; hence `HvdH.slices A m B es` is the concatenation, over `a < A`,
of the columns of `blockOf m B a es`.

Both sides read out of range with `default` (`List.getD _ _ default`), so the length hypothesis on
`es` is not needed for the identity.

The two ingredients are

* `blockOf_getD` — an in-range `getD` of the flat block, which is a `List.map`, is the `getD` of the
  underlying array at the shifted index;
* `flatten_blocks` — flattening `A` blocks of `B` entries is the same as mapping over
  `List.range (A*B)` and re-splitting the index as `s ↦ (s / B, s % B)`.

Public versions of the two ingredients are proved in the sibling files
`Submission/Work/Layout/AA/colsOf_blockOf.lean` and
`Submission/Work/Layout/AA/flatten_map_range_map.lean`.
-/

set_option autoImplicit false

namespace Work.Layout.AA

/-! ## Reading out a flat block -/

/-- In-range read-out of the flat `m × B` block `a` of `es`: entry `t` of the block is entry
`a*(m*B) + t` of the flat array. -/
private lemma blockOf_getD (m B a t : ℕ) (es : List HvdH.Val) (ht : t < m * B) :
    (blockOf m B a es).getD t default = es.getD (a * (m * B) + t) default := by
  unfold blockOf
  have ht' : t < (List.range (m * B)).length := by simpa using ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (l := List.range (m * B)) (i := t) ht']
  simp

/-- The mixed-radix cell `j*B + i` stays inside the block `m × B`, for `j < m` and `i < B`. -/
private lemma mul_add_lt_mul {m B i j : ℕ} (hj : j < m) (hi : i < B) : j * B + i < m * B := by
  have h1 : j * B + i < j * B + B := Nat.add_lt_add_left hi _
  rw [← Nat.succ_mul] at h1
  exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj))

/-- The columns of the block `a` are the slices `a*B + i` of that block. -/
private lemma colsOf_blockOf_aux (m B a : ℕ) (es : List HvdH.Val) :
    colsOf m B (blockOf m B a es) =
      (List.range B).map fun i =>
        (List.range m).map fun j => es.getD ((a * m + j) * B + i) default := by
  unfold colsOf
  refine List.map_congr_left (fun i hi => ?_)
  refine List.map_congr_left (fun j hj => ?_)
  have hj' : j < m := List.mem_range.mp hj
  have hi' : i < B := List.mem_range.mp hi
  have ht : j * B + i < m * B := mul_add_lt_mul hj' hi'
  rw [blockOf_getD m B a (j * B + i) es ht,
    show a * (m * B) + (j * B + i) = (a * m + j) * B + i from by ring]

/-! ## Flattening blocks of equal length -/

/-- Flattening `A` blocks of `B` entries: the entry `i` of block `a` sits at flat index `a*B + i`,
so `((range A).map fun a => (range B).map (F a)).flatten` is the `map` over `range (A*B)` that
re-splits the index as `s ↦ (s / B, s % B)`. -/
private lemma flatten_map_range_map_aux {α : Type} (A B : ℕ) (F : ℕ → ℕ → α) :
    ((List.range A).map fun a => (List.range B).map fun i => F a i).flatten =
      (List.range (A * B)).map fun s => F (s / B) (s % B) := by
  induction A with
  | zero => simp
  | succ A ih =>
    have hL : ((List.range (A + 1)).map fun a => (List.range B).map fun i => F a i).flatten
        = ((List.range A).map fun a => (List.range B).map fun i => F a i).flatten
          ++ (List.range B).map fun i => F A i := by
      rw [List.range_succ, List.map_append]
      simp
    rw [hL, ih]
    have hR : (List.range ((A + 1) * B)).map (fun s => F (s / B) (s % B))
        = (List.range (A * B)).map (fun s => F (s / B) (s % B))
          ++ (List.range B).map (fun x => F ((A * B + x) / B) ((A * B + x) % B)) := by
      rw [Nat.succ_mul, List.range_add, List.map_append, List.map_map]
      rfl
    rw [hR]
    have hmap : (List.range B).map (fun i => F A i)
        = (List.range B).map (fun x => F ((A * B + x) / B) ((A * B + x) % B)) := by
      refine List.map_congr_left (fun x hx => ?_)
      simp only [List.mem_range] at hx
      have hB : 0 < B := by omega
      have h1 : (A * B + x) / B = A := by
        rw [Nat.mul_comm A B, Nat.mul_add_div hB, Nat.div_eq_of_lt hx, Nat.add_zero]
      have h2 : (A * B + x) % B = x := by
        rw [Nat.add_comm (A * B) x, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [h1, h2]
    rw [hmap]

/-- The concrete instance of `flatten_map_range_map_aux` used below, with the flat `A × B` blocks
`(List.range m).map fun j => es.getD ((a*m+j)*B + i) default` of the slices of `es`. -/
private lemma flatten_blocks (A m B : ℕ) (es : List HvdH.Val) :
    ((List.range A).map fun a => (List.range B).map fun i =>
        (List.range m).map fun j => es.getD ((a * m + j) * B + i) default).flatten
      = (List.range (A * B)).map fun s =>
        (List.range m).map fun j => es.getD ((s / B * m + j) * B + s % B) default :=
  flatten_map_range_map_aux A B (fun a i =>
    (List.range m).map fun j => es.getD ((a * m + j) * B + i) default)

/-! ## The main identity -/

theorem slices_eq_blocks (A m B : ℕ) (es : List HvdH.Val) (h : es.length = A * m * B) :
    HvdH.slices A m B es =
      ((List.range A).map fun a =>
        Work.Layout.AA.colsOf m B (Work.Layout.AA.blockOf m B a es)).flatten := by
  -- replace each block by its explicit columns
  have hmapA : (List.range A).map (fun a =>
        Work.Layout.AA.colsOf m B (Work.Layout.AA.blockOf m B a es))
      = (List.range A).map (fun a => (List.range B).map fun i =>
          (List.range m).map fun j => es.getD ((a * m + j) * B + i) default) :=
    List.map_congr_left (fun a _ => colsOf_blockOf_aux m B a es)
  rw [hmapA]
  -- flatten the `A` blocks of `B` columns
  rw [flatten_blocks A m B es]
  -- both sides are now the `A*B` slices, written identically
  unfold HvdH.slices
  rfl

end Work.Layout.AA
