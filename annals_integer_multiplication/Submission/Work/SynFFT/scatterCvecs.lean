import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.axisScatterGetD

/-!
# `scatterCvecs`: flattening `slices A B t` at the level of the `cvecs` of a list of vectors

`HvdH.slices A m B es` cuts a flat `A × m × B` array into its `A*B` slices of length `m`.
For the axis-by-axis synthetic FFT, the array is a list `W` of coefficient vectors and the
value stack carries the *encoded* vectors `cvecs W = W.map cvecVal`.  This file shows that
flattening the slices commutes with the encoding: the flattened list of encoded slices is the
encoding of the scattered array, i.e. of the `List.range`-map of `W` at the scattered index

`i ↦ (i / (t * B) * B + i % B) * t + i / B % t`.

The proof is index bookkeeping:

* `flatten_slices_length`: the flattening of `slices A m B es` has `A * m * B` entries
  (each of the `A*B` slices has length `m`);
* `scatterIdx_lt`: the scattered index of an `i < A*t*B` is again `< A*B*t` (it is the
  bijection underlying the scatter), which is what lets `getD` be replaced by `getElem`;
* `cvecs_getD_default`: `cvecs` commutes with `getD`/`getElem` in range;
* `axisScatterGetD` (already proved in `axisScatterGetD.lean`) reads the flattening of the
  slices of `cvecs W` at a flat index;
* the two lists are then compared entrywise with `List.ext_getElem`.
-/

set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- Every slice of `HvdH.slices A m B es` has length `m` (independently of `es`), hence the
flattening has `A * m * B` entries. -/
theorem flatten_slices_length {α : Type} [Inhabited α] (A m B : ℕ) (es : List α) :
    (List.flatten (HvdH.slices A m B es)).length = A * m * B := by
  simp only [HvdH.slices]
  rw [List.length_flatten, List.map_map]
  have hmap : ((List.range (A * B)).map (List.length ∘ fun s =>
      (List.range m).map fun j => es.getD ((s / B * m + j) * B + s % B) (default : α)))
      = (List.range (A * B)).map (fun _ => m) := by
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, List.length_map, List.length_range]
  rw [hmap, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- `cvecs` commutes with `getD`, in range: the `k`-th encoded vector is the encoding of the
`k`-th vector (`default` of `Val` is *not* `Val.nil`, whence the range hypothesis). -/
theorem cvecs_getD_default (W : List (List (ℤ × ℤ))) (k : ℕ) (hk : k < W.length) :
    (cvecs W).getD k (default : HvdH.Val) = HvdH.cvecVal (W.getD k []) := by
  rw [List.getD_eq_getElem _ (default : HvdH.Val) (by simpa [cvecs] using hk)]
  simp only [cvecs]
  rw [List.getElem_map, ← List.getD_eq_getElem _ ([] : List (ℤ × ℤ)) hk]

/-- The scattered index of a flat index `i < A * t * B` is again a flat index, `< A * B * t`:
the scatter `i ↦ (i / (t*B) * B + i % B) * t + i / B % t` permutes `[0, A*t*B)`. -/
theorem scatterIdx_lt (A t B i : ℕ) (hi : i < A * t * B) :
    (i / (t * B) * B + i % B) * t + i / B % t < A * B * t := by
  have hpos : 0 < A * t * B := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hpos; exact Nat.lt_irrefl 0 hpos
  have hAt : 0 < A * t := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.zero_mul] at hpos; exact Nat.lt_irrefl 0 hpos
  have hA : 0 < A := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.zero_mul] at hAt; exact Nat.lt_irrefl 0 hAt
  have ht : 0 < t := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hAt; exact Nat.lt_irrefl 0 hAt
  have hi' : i < A * (t * B) := by rwa [Nat.mul_assoc] at hi
  have h1 : i / (t * B) < A := (Nat.div_lt_iff_lt_mul (Nat.mul_pos ht hB)).mpr hi'
  have h2 : i % B < B := Nat.mod_lt _ hB
  have hs : i / (t * B) * B + i % B < A * B := by
    have h3 : i / (t * B) * B + i % B < (i / (t * B) + 1) * B := by
      have he : (i / (t * B) + 1) * B = i / (t * B) * B + B := by ring
      rw [he]; omega
    exact lt_of_lt_of_le h3 (Nat.mul_le_mul_right B (by omega))
  have hj : i / B % t < t := Nat.mod_lt _ ht
  have h4 : ((i / (t * B) * B + i % B) + 1) * t ≤ (A * B) * t :=
    Nat.mul_le_mul_right t (by omega)
  have he : ((i / (t * B) * B + i % B) + 1) * t = (i / (t * B) * B + i % B) * t + t := by ring
  rw [he] at h4
  omega

theorem scatterCvecs (A t B : ℕ) (W : List (List (ℤ × ℤ))) (h : W.length = A * B * t) :
    List.flatten (HvdH.slices A B t (Work.SynFFT.cvecs W))
      = Work.SynFFT.cvecs ((List.range (A * t * B)).map fun i =>
          W.getD ((i / (t * B) * B + i % B) * t + i / B % t) []) := by
  -- the right-hand side is a `List.range`-map of the encoded vectors
  have hR : Work.SynFFT.cvecs ((List.range (A * t * B)).map fun i =>
        W.getD ((i / (t * B) * B + i % B) * t + i / B % t) [])
      = (List.range (A * t * B)).map fun i =>
          HvdH.cvecVal (W.getD ((i / (t * B) * B + i % B) * t + i / B % t) []) := by
    rw [Work.SynFFT.cvecs, List.map_map]
    rfl
  rw [hR]
  refine List.ext_getElem ?_ ?_
  · -- both sides have `A * t * B` entries
    rw [flatten_slices_length, List.length_map, List.length_range]
    ring
  · -- entrywise comparison
    intro i h1 h2
    have hi : i < A * t * B := by simpa using h2
    have hlen : (Work.SynFFT.cvecs W).length = A * B * t := by
      simp [Work.SynFFT.cvecs, h]
    have hgi : ((i / (t * B) * B + i % B) * t + i / B % t) < W.length := by
      rw [h]; exact scatterIdx_lt A t B i hi
    -- read both sides with `getD` (`axisScatterGetD` is a `getD` statement)
    rw [← List.getD_eq_getElem _ (default : HvdH.Val) h1,
        ← List.getD_eq_getElem _ (default : HvdH.Val) h2]
    rw [axisScatterGetD A t B (Work.SynFFT.cvecs W) hlen i hi,
        Work.SynFFT.getD_map_range _ (default : HvdH.Val) hi]
    exact cvecs_getD_default W _ hgi

end Work.SynFFT
