import Mathlib
import Submission.Work.SynFFT.axisKit

namespace Work.SynFFT

open HvdH

/-!
# `colsTranspose`

`cols` (`Submission/Work/SynFFT/axisKit.lean`) is the transpose of a matrix presented as a list of
rows, computed by the leaf/merge recursion `cols (r :: rs) = zipCat (exploded r) (cols rs)`.

This file proves the elementary description of `cols` used by the axis/transpose words: for a
nonempty family of rows all of length `n`, the `b`-th column is the list of the `b`-th entries of
the rows.
-/

/-- `zipCat` of two lists of rows of equal length is their pointwise concatenation. -/
private theorem zipCat_map_map_append (l : List ℕ) (f g : ℕ → List Val) :
    zipCat (l.map f) (l.map g) = l.map (fun b => f b ++ g b) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, zipCat, ih]

/-- A row exploded into its singleton columns is the transpose of the `1 × length` matrix. -/
private theorem exploded_eq_range (r : List Val) :
    exploded r = (List.range r.length).map (fun b => [r.getD b Val.nil]) := by
  unfold exploded
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map]
    rw [List.getElem_range (by simpa using h2), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h1)]
    rfl

/-- The transpose of a matrix presented as a list of rows, read off by columns. -/
private def colTr (rows : List (List Val)) (n : ℕ) : List (List Val) :=
  (List.range n).map (fun b => rows.map (fun s => s.getD b Val.nil))

/-- One recursion step of the transpose, matching the definition of `cols`. -/
private theorem colTr_cons (r : List Val) (rs : List (List Val)) (n : ℕ)
    (hr : r.length = n) : colTr (r :: rs) n = zipCat (exploded r) (colTr rs n) := by
  unfold colTr
  rw [exploded_eq_range, hr, zipCat_map_map_append]
  simp only [List.singleton_append, List.map_cons]

/-- `cols` agrees with the column description, for a nonempty list of rows of common length. -/
private theorem cols_eq_colTr (rows : List (List Val)) (n : ℕ) (hne : rows ≠ [])
    (hlen : ∀ s ∈ rows, s.length = n) : cols rows = colTr rows n := by
  induction rows with
  | nil => exact absurd rfl hne
  | cons r rs ih =>
    rcases rs with _ | ⟨s, ss⟩
    · have hr : r.length = n := hlen r (by simp)
      show cols [r] = colTr [r] n
      rw [cols_singleton, exploded_eq_range, hr]
      unfold colTr
      simp only [List.map_cons, List.map_nil]
    · have hrs_ne : (s :: ss) ≠ [] := by simp
      have hrs_len : ∀ x ∈ (s :: ss), x.length = n :=
        fun x hx => hlen x (List.mem_cons_of_mem r hx)
      have ih' : cols (s :: ss) = colTr (s :: ss) n := ih hrs_ne hrs_len
      have hr : r.length = n := hlen r (by simp)
      show zipCat (exploded r) (cols (s :: ss)) = colTr (r :: s :: ss) n
      rw [colTr_cons r (s :: ss) n hr, ih']

theorem colsTranspose (rows : List (List HvdH.Val)) (n : ℕ)
    (hne : rows ≠ []) (hlen : ∀ s ∈ rows, s.length = n) :
    cols rows = (List.range n).map (fun b => rows.map (fun s => s.getD b HvdH.Val.nil)) :=
  cols_eq_colTr rows n hne hlen

end Work.SynFFT
