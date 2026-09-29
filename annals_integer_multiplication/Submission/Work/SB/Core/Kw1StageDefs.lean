import Mathlib
import Submission.Work.Layout.Shared

/-!
# Vocabulary for the first (`kw1`) labelling stage

The stage takes the flat payload list `es` (length `A * m * B`, each element extended by its flat
index `i`) and relabels every element with its **slice-major** label `keyIdx1 m B i`, keeping the
payload and the three parameter values `m`, `B`, `A` below it.

`kw1In`/`kw1Out` are the input/output lists produced by the per-element word `kw1`
(`Work.Layout.Kw1Spec`), which sees `cons (int i) v :: int m :: int B :: tail` and returns
`cons (int (keyIdx1 m B i)) v :: int m :: int B :: tail`.
-/

set_option autoImplicit false

namespace Work.SB.Core

open HvdH

/-- The labelled input list of the first labelling stage: flat index `i` stored in the payload. -/
def kw1In (A m B : ℕ) (es : List Val) : List Val :=
  (List.range (A * m * B)).map fun i => Val.cons (Val.int ((i : ℕ) : ℤ)) (es.getD i Val.nil)

/-- The labelled output list of the first labelling stage: slice-major label `keyIdx1 m B i`. -/
def kw1Out (A m B : ℕ) (es : List Val) : List Val :=
  (List.range (A * m * B)).map fun i =>
    Val.cons (Val.int ((Work.Layout.keyIdx1 m B i : ℕ) : ℤ)) (es.getD i Val.nil)

/-- Precondition of the per-element word `kw1`: `x = cons (int i) v` with `i` a flat index of the
payload and `x` of size `≤ L + N.size + 3` (`L` bounds the payload, `N.size` the index). -/
def kw1P (A m B N L : ℕ) : Val → Prop := fun x =>
  ∃ (i : ℕ) (v : Val), i < A * m * B ∧ x = Val.cons (Val.int ((i : ℕ) : ℤ)) v ∧
    vsz x ≤ L + N.size + 3

/-- Postcondition of the per-element word `kw1`: the label `i` becomes `keyIdx1 m B i`, the payload
`v` and everything else is kept. -/
def kw1Q (A m B : ℕ) : Val → Val → Prop := fun x y =>
  ∃ (i : ℕ) (v : Val), i < A * m * B ∧ x = Val.cons (Val.int ((i : ℕ) : ℤ)) v ∧
    y = Val.cons (Val.int ((Work.Layout.keyIdx1 m B i : ℕ) : ℤ)) v

/-- Size bound on the output of the per-element word, with payload bound `L` and index bound `N`. -/
def kw1SizeOut (N L : ℕ) : ℕ := L + N.size + 3 + N.size + 2

/-- Cost bound of the per-element word, with constant `K`, payload bound `L` and index bound `N`. -/
def kw1ElemCost (K N L : ℕ) : ℕ := K * (L + N.size + 3 + N.size + 2) * (N.size + 2)

@[simp] theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [HvdH.vsz, HvdH.Val.enc]

theorem kw1In_length (A m B : ℕ) (es : List Val) : (kw1In A m B es).length = A * m * B := by
  simp [kw1In]

end Work.SB.Core
