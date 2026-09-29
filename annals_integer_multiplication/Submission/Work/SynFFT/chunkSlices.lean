import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# Slicing the flattening of `HvdH.slices`

`HvdH.slices A t B es` is the list of the `A*B` slices of a flat `A × t × B` array: slice `s` is
`j ↦ es[(s / B * t + j) * B + s % B]`, `j < t`.  Every slice has length exactly `t`, so flattening
and cutting out the `s`-th block of `t` consecutive entries recovers slice `s`:

    ((List.flatten (HvdH.slices A t B es)).drop (s * t)).take t = (HvdH.slices A t B es).getD s []

This is the list identity used by the `applyAlong`-based synthetic-FFT assembly when it re-reads a
slice of the flat array out of the flattened slice list.

The mathematical content is a general list fact (`flatten_map_drop_take`): if `g` maps every element
of `l` to a list of length `n`, then dropping `s * n` and taking `n` from `(l.map g).flatten`
extracts the `s`-th of those lists.

An out-of-range read on either side goes through `List.getD _ _ []`, so nothing on the length of
`es` is needed (`h` is part of the requested statement only).
-/

set_option autoImplicit false

namespace Work.SynFFT

/-- **Block extraction from a flattened list of equal-length lists.**
If every list in `l.map g` has length `n` and `s < l.length`, then dropping `s * n` and taking `n`
from `(l.map g).flatten` gives back the `s`-th list. -/
lemma flatten_map_drop_take {α β : Type} (l : List α) (g : α → List β) (n s : ℕ)
    (hlen : ∀ i ∈ l, (g i).length = n) (hs : s < l.length) :
    (((l.map g).flatten).drop (s * n)).take n = (l.map g).getD s [] := by
  induction l generalizing s with
  | nil => simp at hs
  | cons x t ih =>
    rw [List.map_cons, List.flatten_cons]
    cases s with
    | zero =>
      have hgx : (g x).length = n := hlen x (by simp)
      simp only [Nat.zero_mul, List.drop_zero, List.getD_cons_zero]
      rw [← hgx]
      exact List.take_left
    | succ s =>
      have hgx : (g x).length = n := hlen x (by simp)
      have hst : s < t.length := by
        simp only [List.length_cons] at hs; omega
      have hlen' : ∀ i ∈ t, (g i).length = n := fun i hi => hlen i (by simp [hi])
      rw [List.getD_cons_succ]
      have hdrop : (g x ++ (t.map g).flatten).drop ((s + 1) * n)
          = ((t.map g).flatten).drop (s * n) := by
        have h1 : (s + 1) * n = n + s * n := by ring
        have h2 : (g x ++ (t.map g).flatten).drop n = (t.map g).flatten := by
          rw [← hgx]; exact List.drop_left
        rw [h1, ← List.drop_drop, h2]
      rw [hdrop]
      exact ih s hlen' hst

/-- Every `getD`-in-range slice of `HvdH.slices` has length `t`. -/
lemma slices_getD_length (A t B : ℕ) (es : List HvdH.Val) {s : ℕ} (hs : s < A * B) :
    ((HvdH.slices A t B es).getD s []).length = t := by
  unfold HvdH.slices
  rw [List.getD_eq_getElem _ _ (by simpa using hs)]
  simp

theorem chunkSlices (A t B : ℕ) (es : List HvdH.Val) (h : es.length = A * t * B) (s : ℕ)
    (hs : s < A * B) :
    ((List.flatten (HvdH.slices A t B es)).drop (s * t)).take t = (HvdH.slices A t B es).getD s [] := by
  have _hes := h
  unfold HvdH.slices
  refine flatten_map_drop_take (List.range (A * B)) (fun s => (List.range t).map fun j =>
    es.getD ((s / B * t + j) * B + s % B) default) t s ?_ ?_
  · intro i _
    simp
  · simpa using hs

end Work.SynFFT
