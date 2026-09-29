import Mathlib
import Submission.Work.Resample.tensorAux

/-!
# Length of the iterated axis pass `axisIter`

`Work.Resample.axisIter ss ts Φ k es` applies the slice map `Φ i` along the axes `0, …, k-1`,
each pass being a `Work.Resample.axisList A m n B` (the `HvdH.slices`/`unslices` layout of
`HvdH.LayoutLib.applyAlong`).  The point of this file is that such a pass is a pure reshaping:
its length is the *shape* `A * n * B` of the output array, and does not depend on the input list
at all (both `slices` and `unslices` are defined with `getD`, so no length/structure hypothesis is
involved).  Consequently the length after `k` passes is

`(ts.take k).prod * (ss.drop k).prod`

— the product of the output lengths `ts i` over the axes already processed times the product of
the input lengths `ss j` over the axes still to come — which is what `axisIter_length` records.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- A single axis pass `axisList A m n B Φ` is a reshaping: its length is the shape of the output
array `A × n × B`, independently of the input list. -/
lemma axisList_length_axisIter_length (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (es : List (ℤ × ℤ)) : (axisList A m n B Φ es).length = A * n * B := by
  simp [axisList, HvdH.unslices]

/-- Splitting off the last factor of a `take`: `(ts.take (k+1)).prod = (ts.take k).prod * ts k`
when `ts k` is read as `ts.getD k 0` (valid since `k < ts.length`). -/
lemma take_succ_prod (ts : List ℕ) (k : ℕ) (hk : k < ts.length) :
    (ts.take (k + 1)).prod = (ts.take k).prod * ts.getD k 0 := by
  rw [List.take_succ_eq_append_getElem hk, List.getD_eq_getElem ts 0 hk, List.prod_append]
  simp

theorem axisIter_length (ss ts : List ℕ) (hl : ts.length = ss.length) (k : ℕ)
    (hk : k ≤ ss.length) (hpos : ∀ j < k, 0 < ss.getD j 0)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (es : List (ℤ × ℤ)) (hlen : es.length = (ss.take k).prod * (ss.drop k).prod) :
    (Work.Resample.axisIter ss ts Φ k es).length = (ts.take k).prod * (ss.drop k).prod := by
  rcases k with _ | k
  · -- no axis processed: the array is returned unchanged
    simpa [axisIter] using hlen
  · -- one axis pass: it replaces the factor `ss k` of the shape by `ts k`
    have hklt : k < ts.length := by omega
    rw [axisIter, axisList_length_axisIter_length, take_succ_prod ts k hklt]

end Work.Resample
