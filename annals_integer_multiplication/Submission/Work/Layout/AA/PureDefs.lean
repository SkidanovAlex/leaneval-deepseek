import Mathlib
import Submission.HvdH.Interfaces

/-!
# Pure list layer for the `applyAlong` implementation

Flat arrays of `Val`s are `List Val`; a flat `m × C` array is the row-major flattening of `m` rows of
`C` elements.  This file defines

* `rowsOf m C L` / `colsOf m C L` — the rows / columns of the flat list `L`;
* `blockOf m B a es` — the `a`-th block (flat `m × B` array) of the flat `A × m × B` array `es`;
* `transposeC C L` — the recursive "split the columns in half, recurse, concatenate" transposition
  used by the DFS loop of the implementation; its leaves are the columns;
* `splitProc C1 C2 rows` — the pure content of the partition step of the DFS.  The DFS first reverses
  the flat chunk; the rows of the reversed chunk are `rows.map List.reverse` for the original rows.
  The partition pops the rows in order, taking `C2 = ⌈C/2⌉` elements (`C1 = ⌊C/2⌋` next) and building
  the two outputs by prepending; `splitProc` records the resulting pair of lists.
-/

set_option autoImplicit false

namespace Work.Layout
namespace AA

open HvdH

/-- The rows of a flat `m × C` array. -/
def rowsOf (m C : ℕ) (L : List Val) : List (List Val) :=
  (List.range m).map fun j => (List.range C).map fun i => L.getD (j * C + i) default

/-- The columns of a flat `m × C` array. -/
def colsOf (m C : ℕ) (L : List Val) : List (List Val) :=
  (List.range C).map fun i => (List.range m).map fun j => L.getD (j * C + i) default

/-- The `a`-th block of a flat `A × m × B` array: its flat `m × B` form. -/
def blockOf (m B a : ℕ) (es : List Val) : List Val :=
  (List.range (m * B)).map fun t => es.getD (a * (m * B) + t) default

/-- Fuel version of the recursive transposition: `transposeCAux fuel C L` splits the flat `m × C`
array `L` by halving `C` (at most `fuel` times, which is enough when started with `C`). -/
def transposeCAux : ℕ → ℕ → List Val → List (List Val)
  | 0, _, _ => []
  | _ + 1, 0, _ => []
  | _ + 1, 1, L => [L]
  | fuel + 1, C + 2, L =>
      let C1 := (C + 2) / 2
      let C2 := C + 2 - C1
      let m := L.length / (C + 2)
      let A := ((List.range m).map fun j =>
        ((List.range C1).map fun i => L.getD (j * (C + 2) + i) default)).flatten
      let B := ((List.range m).map fun j =>
        ((List.range C2).map fun i => L.getD (j * (C + 2) + C1 + i) default)).flatten
      transposeCAux fuel C1 A ++ transposeCAux fuel C2 B

/-- The columns of the flat `m × C` array `L`, computed by the recursive halving performed by the
DFS loop. -/
def transposeC (C : ℕ) (L : List Val) : List (List Val) := transposeCAux C C L

/-- Pure content of the partition step of the DFS, given the rows of the *reversed* chunk. -/
def splitProc : ℕ → ℕ → List (List Val) → List Val × List Val
  | _, _, [] => ([], [])
  | C1, C2, r :: rs =>
      let p := splitProc C1 C2 rs
      (p.1 ++ (r.drop C2).reverse, p.2 ++ (r.take C2).reverse)

end AA
end Work.Layout
