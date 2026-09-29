import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.defs
import Submission.Work.Resample.axis

/-!
# List-level bookkeeping for the tensoring program (paper Thm 4.1)

`Work.Resample.axisList` is the *list*-level formulation of one `HvdH.LayoutLib.applyAlong` call:
it applies a fixed-point slice map `Φ` to every slice of a flat array `es` of shape `A × m × B`
(in the `HvdH.slices` / `HvdH.unslices` layout of `applyAlong`) and reassembles the result into a
flat array of shape `A × n × B`.

`Work.Resample.axisIter` iterates this over the axes `0, 1, …, k-1` with the layout parameters
`A = ∏_{j<i} ts_j`, `m = ss_i`, `n = ts_i`, `B = ∏_{j>i} ss_j`, i.e. in exactly the order in which
the tensoring program walks the axes of the array.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Apply the slice map `Φ` to every `s`-slice of the flat array `es` (shape `A × m × B`) and
reassemble into a flat array of shape `A × n × B`. -/
noncomputable def axisList (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (es : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  HvdH.unslices A n B ((List.range (A * B)).map fun s =>
    List.ofFn fun j : Fin n =>
      Φ (fun i : Fin m => ((HvdH.slices A m B es).getD s []).getD i (0, 0)) j)

/-- `axisIter ss ts Φ k es` applies `Φ 0, …, Φ (k-1)` along the successive axes. -/
noncomputable def axisIter (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) :
    ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, es => es
  | k + 1, es => axisList ((ts.take k).prod) (ss.getD k 0) (ts.getD k 0) ((ss.drop (k + 1)).prod)
      (Φ k) (axisIter ss ts Φ k es)

end Work.Resample
