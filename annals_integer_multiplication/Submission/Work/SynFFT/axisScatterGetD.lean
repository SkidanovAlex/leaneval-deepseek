import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.lvlAllGetD

/-!
# `axisScatterGetD`: reading `List.flatten (HvdH.slices A B t g)` at a flat index

`HvdH.slices A m B g` cuts the flat array `g` (of total length `A * m * B`, shape `A × m × B`,
last index fastest) into the `A * B` slices `s ↦ (j ↦ g[(s / B * m + j) * B + s % B])`,
`j < m`.  Concatenating them *scatters* the entries: reading the flattened list at a flat
index `i` (with `i < A * t * B` for the instantiation `m = B`, `B = t` below) recovers the
entry of `g` at the scattered position `(i / (t * B) * B + i % B) * t + i / B % t`.

This is the index bookkeeping used by the axis-by-axis (`applyAlong`) scatter/unscatter of the
synthetic FFT.  The proof is pure list plumbing: split `i = (i / B) * B + i % B` into block
index and in-block offset, read the concatenation of equal-length blocks
(`getD_flatten_eq`), read the `List.range`-indexed slice list (`getD_map_range`), and compare
`i / B / t = i / (t * B)`.
-/

set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

theorem axisScatterGetD (A t B : ℕ) (g : List HvdH.Val) (h : g.length = A * B * t) (i : ℕ)
    (hi : i < A * t * B) :
    (List.flatten (HvdH.slices A B t g)).getD i (default : HvdH.Val)
      = g.getD ((i / (t * B) * B + i % B) * t + i / B % t) (default : HvdH.Val) := by
  -- `B ≠ 0`, because `i < A * t * B`
  have hBpos : 0 < B := by
    by_contra hB
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos hB
    subst hB0
    simp at hi
  -- the block index of `i` is a valid slice index, and the offset is a valid in-block index
  have hb : i / B < A * t := (Nat.div_lt_iff_lt_mul hBpos).mpr hi
  have hj : i % B < B := Nat.mod_lt _ hBpos
  -- unfold the `slices` definition once and for all
  simp only [HvdH.slices]
  -- all the slices have length `B`
  have hlen : ∀ l ∈ (List.range (A * t)).map (fun s => (List.range B).map
      (fun j => g.getD ((s / t * B + j) * t + s % t) (default : HvdH.Val))), l.length = B := by
    intro l hl
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hl
    simp
  -- read the concatenation of the slices at flat index `i = (i / B) * B + i % B`
  have h1 := getD_flatten_eq
    (L := (List.range (A * t)).map (fun s => (List.range B).map
      (fun j => g.getD ((s / t * B + j) * t + s % t) (default : HvdH.Val))))
    (d := (default : HvdH.Val)) (n := B) hlen (i / B) (i % B) hj
  rw [Nat.mul_comm (i / B) B, Nat.div_add_mod] at h1
  rw [h1]
  -- read the slice list at the block index
  have h2 := getD_map_range
    (f := fun s => (List.range B).map
      (fun j => g.getD ((s / t * B + j) * t + s % t) (default : HvdH.Val)))
    (d := ([] : List HvdH.Val)) (n := A * t) hb
  rw [h2]
  -- read the slice itself at the in-block offset
  have h3 := getD_map_range
    (f := fun j => g.getD ((i / B / t * B + j) * t + (i / B) % t) (default : HvdH.Val))
    (d := (default : HvdH.Val)) (n := B) hj
  rw [h3]
  -- `i / B / t = i / (t * B)`
  rw [show i / B / t = i / (t * B) by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]]

end Work.SynFFT
