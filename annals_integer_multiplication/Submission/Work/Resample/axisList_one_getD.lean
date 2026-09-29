import Mathlib
import Submission.Work.Resample.axKit
import Submission.Work.Resample.tensorAux

/-!
# Reading one entry of a single-axis `axisList` pass

`Work.Resample.axisList A m n B Φ es` applies the slice map `Φ` to every one of the `A * B`
slices (of length `m`) of the flat array `es` and reassembles the results (of length `n`) into a
flat array of shape `A × n × B`.

For `A = 1` the array is a single `m × B` matrix: the axis map acts on the *rows* (the `m`-axis),
so the output entry at flat index `g * B + i` (`g < n`, `i < B`) is `Φ` applied to the input
column `j ↦ es[j * B + i]`, at row `g`. That is the content of `axisList_one_getD` below; it is
the `A = 1` case of the entrywise description of one axis pass that the tensor recursion
(`axisIter_getD_fxTensorRec`) needs.

The two ingredients are the elementary read-outs of `HvdH.slices` and `HvdH.unslices` with
`A = 1` (`slices_one_getD_row`, `unslices_one_getD_slice`), both proved by unwinding the
definitions and doing the index arithmetic of `Nat` division and remainder.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-! ## Read-out of the layout combinators with a single outer block -/

/-- With `A = 1`, slice `i < B` of the `1 × m × B` array `es` is the `i`-th column of the
`m × B` matrix: the map `j ↦ es[j * B + i]`.  Slices are read out with `getD`, so no length
hypothesis on `es` is needed. -/
lemma slices_one_getD_row (m B : ℕ) (es : List (ℤ × ℤ)) (i : ℕ) (hi : i < B) :
    (HvdH.slices 1 m B es).getD i [] =
      (List.range m).map (fun j => es.getD (j * B + i) (0,0)) := by
  unfold HvdH.slices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp only [Nat.one_mul]; exact hi), Option.map_some, Option.getD_some]
  apply List.map_congr_left
  intro j hj
  rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
  simp only [Nat.zero_mul, Nat.zero_add]
  rfl

/-- With `A = 1`, the flat entry `g * B + i` of `HvdH.unslices 1 n B outs` (`g < n`, `i < B`)
is the `g`-th entry of slice `i`: the slices are laid out as `n` rows of `B` entries, row `g`
being the `B` consecutive entries `outs[i][g]` (`i < B`). -/
lemma unslices_one_getD_slice (n B : ℕ) (outs : List (List (ℤ × ℤ))) (g i : ℕ) (hg : g < n)
    (hi : i < B) :
    (HvdH.unslices 1 n B outs).getD (g * B + i) (0,0) = (outs.getD i []).getD g (0,0) := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le i) hi
  have hlt : g * B + i < n * B := Work.Resample.mul_add_lt_mul hg hi
  unfold HvdH.unslices
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp only [Nat.one_mul]; exact hlt),
    Option.map_some, Option.getD_some]
  have hmod : (g*B + i) % B = i := by
    rw [Nat.mul_comm g B, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hdiv : (g*B + i) / B = g := by
    rw [Nat.mul_comm g B, Nat.mul_add_div hB, Nat.div_eq_of_lt hi, Nat.add_zero]
  rw [Nat.div_eq_of_lt hlt, hmod, hdiv, Nat.mod_eq_of_lt hg]
  simp only [Nat.zero_mul, Nat.zero_add]
  rfl

/-! ## The main entrywise description -/

theorem axisList_one_getD (s t B : ℕ) (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) (ht : 0 < t) (hB : 0 < B) (g i : ℕ) (hg : g < t) (hi : i < B) :
    (Work.Resample.axisList 1 s t B Φ zs).getD (g * B + i) (0,0) =
      Φ (fun j : Fin s => zs.getD ((j : ℕ) * B + i) (0,0)) ⟨g, hg⟩ := by
  -- unwind the definition: `axisList 1 s t B Φ zs` is `unslices 1 t B` of the list of the
  -- images of the `B` columns of `zs`
  rw [axisList, Nat.one_mul]
  -- read the flat entry `g * B + i` of `unslices 1 t B`
  rw [unslices_one_getD_slice t B _ g i hg hi]
  -- it is entry `g` of slice `i < B`, i.e. of the image of column `i`
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [List.getElem?_ofFn, dite_eq_left hg, Option.getD_some]
  -- it remains to identify the argument of `Φ`: column `i` of the `1 × s × B` array `zs`
  congr 1
  funext j
  rw [slices_one_getD_row s B zs i hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Option.getD_some]

end Work.Resample
