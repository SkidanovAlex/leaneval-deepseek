import Mathlib
import Submission.Work.Layout.SB.Specs

set_option autoImplicit false

/-!
# Shared vocabulary for the `branchWord2` (slices step) proof

`branchWord2` builds the word that turns `ofList es :: int m :: int B :: int A :: rest` into
`ofList ((slices A m B es).map ofList) :: rest` (the `A*B` slices of the flat `A × m × B` array
`es`, as a list of list-values), at cost `O((N+1)*(L+N.size+1)*(N.size+1) + isz A + isz m + isz B)`
whenever `A*m*B ≤ N`, `A*B ≤ N`, `es.length = A*m*B` and every entry of `es` has `vsz ≤ L`.

The word is assembled from three mutually independent forced branches:

* `degWord`   (`m = 0`): `slices A 0 B es = List.replicate (A*B) []`, so the answer is
  `ofList (List.replicate (A*B) .nil)`; the word drops the three integers and rebuilds
  `int (A*B) :: .nil` (product `int B * int A`, `pushVal .nil`, `swap`) before `replicate`.
* `bzeroWord` (`B = 0`): then `A*B = 0` and `es = []`, so the answer is `.nil :: rest`.
* `bgenWord`  (`0 < m`, `B ≠ 0`): `phase1` (sort-based slices) followed by `chunksOf m`, then the
  two remaining integers are dropped.

The two tests `m = 0` and `B = 0` are made on *copies* (`KernelLib.pick`), so that the value list
below is never disturbed; that is what keeps the branch programs free of static parameters.
-/

namespace Work.SB.BW2

open HvdH
open Work.Layout

/-- The size factor of the `branchWord2` cost. -/
def BIG (N L : ℕ) : ℕ := (N + 1) * (L + N.size + 1) * (N.size + 1)

/-- The integer-size part of the `branchWord2` cost. -/
def S (A m B : ℕ) : ℕ := isz (A : ℤ) + isz (m : ℤ) + isz (B : ℤ)

/-- Entry value list of `branchWord2` and of each of its forced branches. -/
abbrev Pre (A m B : ℕ) (es rest : List Val) : List Val → Prop :=
  fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

/-- Exit value list of `branchWord2` (and of each forced branch). -/
abbrev Post (A m B : ℕ) (es rest : List Val) : List Val → List Val → Prop :=
  fun _ out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧
    sls = slices A m B es

end Work.SB.BW2
