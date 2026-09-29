import Mathlib
import Submission.Work.Layout.enumDefs
import Submission.Work.IntLib.encodeNatBridge

/-!
# Layout: the size of the enumerated (labelled) list

`lab 0 xs` replaces element `j` of `xs` by `Val.cons (.int j) xs[j]`; its `ofList` encoding
therefore consists of the encodings of the elements of `xs`, each preceded by a `cons` glyph and
an `int j` label (and both encodings close with the same `nil`).  The size estimate
`vsz (ofList (lab 0 xs)) ≤ vsz (ofList xs) + 4 * (N * (N.size + 1) + 1)` (with `N = xs.length`)
is used by the `LayoutLib.enumerate` cost analysis: the labels cost at most `isz j ≤ N.size + 2`
glyphs each, and the slack absorbs the `N` extra `cons` glyphs.
-/

namespace Work.Layout

open HvdH

/-- `vsz` of an integer value is `isz`. -/
theorem vsz_int_val (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

/-- Mapping `f` over `xs.getD · d` along `List.range xs.length` recovers `xs.map f`. -/
theorem map_range_getD (f : Val → ℕ) (d : Val) (xs : List Val) :
    (List.range xs.length).map (fun j => f (xs.getD j d)) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hcomp : List.map ((fun j => f ((x :: xs).getD j d)) ∘ Nat.succ) (List.range xs.length)
          = List.map (fun j => f (xs.getD j d)) (List.range xs.length) := by
        apply List.map_congr_left
        intro k _
        simp [Function.comp_apply]
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.getD_cons_zero, hcomp, ih]
      rfl

/-- `lab 0` with the counter at `0`. -/
theorem lab_zero (xs : List Val) :
    lab 0 xs = (List.range xs.length).map (fun j : ℕ => Val.cons (.int (j : ℤ)) (xs.getD j .nil)) := by
  simp only [lab]
  congr 2
  funext j
  simp

/-- Splitting the sum of the sizes of the labelled elements into the label sizes, the element
sizes and the `cons` glyphs. -/
theorem sum_lab_split (xs : List Val) :
    ((List.range xs.length).map (fun j : ℕ => isz ((j : ℤ)) + vsz (xs.getD j .nil) + 1)).sum
      = ((List.range xs.length).map (fun j : ℕ => isz ((j : ℤ)))).sum
        + ((List.range xs.length).map (fun j : ℕ => vsz (xs.getD j .nil))).sum
        + ((List.range xs.length).map (fun _ => (1 : ℕ))).sum := by
  simp only [List.sum_map_add]

/-- Size of the labelled list: `lab 0 xs` is `xs` with element `j` replaced by
`Val.cons (.int j) xs[j]`, so its encoding keeps the encodings of the elements and adds one `int j`
label per element. Hence `vsz (ofList (lab 0 xs)) ≤ vsz (ofList xs) + 4*(N*(N.size+1) + 1)`,
because `isz j = j.size + 2 ≤ N.size + 2` for `j < N = xs.length` (and both lists have `N` elements,
whose `cons` glyphs cancel). -/
theorem vsz_ofList_lab_le (xs : List HvdH.Val) :
    HvdH.vsz (HvdH.ofList (Work.Layout.lab 0 xs)) ≤
      HvdH.vsz (HvdH.ofList xs) + 4 * (xs.length * (xs.length.size + 1) + 1) := by
  have hmap : ((lab 0 xs).map vsz)
      = (List.range xs.length).map (fun j : ℕ => isz ((j : ℤ)) + vsz (xs.getD j .nil) + 1) := by
    rw [lab_zero, List.map_map]
    apply List.map_congr_left
    intro j _
    simp [Function.comp_apply, vsz_enc_cons, vsz_int_val]
  have hget : ((List.range xs.length).map (fun j : ℕ => vsz (xs.getD j .nil))).sum
      = (xs.map vsz).sum := by
    rw [map_range_getD]
  have hone : ((List.range xs.length).map (fun _ => (1 : ℕ))).sum = xs.length := by
    simp [List.sum_replicate]
  have hisz : ((List.range xs.length).map (fun j : ℕ => isz ((j : ℤ)))).sum
      ≤ xs.length * (xs.length.size + 2) := by
    have hpt : ∀ j : ℕ, j ∈ List.range xs.length → isz ((j : ℤ)) ≤ xs.length.size + 2 := by
      intro j hj
      have hj' : j < xs.length := List.mem_range.mp hj
      have h1 : isz ((j : ℤ)) = j.size + 2 := by simp [isz]
      have h2 : j.size ≤ xs.length.size := Nat.size_le_size (Nat.le_of_lt hj')
      omega
    calc ((List.range xs.length).map (fun j : ℕ => isz ((j : ℤ)))).sum
        ≤ ((List.range xs.length).map (fun _ => xs.length.size + 2)).sum :=
          List.sum_le_sum (fun j hj => hpt j hj)
      _ = xs.length * (xs.length.size + 2) := by
          simp [List.sum_replicate]
  have hsum : ((lab 0 xs).map vsz).sum
      ≤ (xs.map vsz).sum + xs.length * (xs.length.size + 2) + xs.length := by
    rw [hmap, sum_lab_split xs, hget, hone]
    linarith
  have harith : xs.length * (xs.length.size + 2) + xs.length
      ≤ 4 * (xs.length * (xs.length.size + 1) + 1) := by nlinarith
  rw [vsz_ofList_en, vsz_ofList_en, lab_length]
  linarith [hsum, harith]

end Work.Layout
