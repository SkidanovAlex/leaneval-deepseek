import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-!
# `zassoc_m9vecZ_add`

Additivity of the flat integer matrix–vector product `m9vecZ` in its second argument:

`m9vecZ a (v + w) = m9vecZ a v + m9vecZ a w`

(componentwise, for `v`, `w` of equal length — without that hypothesis `List.zipWith`
truncates and `getD` pads with `0`, which is exactly the obstruction).

This is one node of the associativity proof for the integer affine product `zMul`
(see `Submission/Work/SG/zMul_assoc.lean`): the translation part of
`(u + A·v) + A·B·w` needs `A·v + A·(B·w) = A·(v + B·w)`.
-/

/-- `getD` of a pointwise sum of two lists of equal length: the padding with `0`
outside the common length is compatible with addition. -/
private theorem zipWith_getD_add (v w : List ℤ) (h : v.length = w.length) (k : ℕ) :
    (List.zipWith (· + ·) v w).getD k 0 = v.getD k 0 + w.getD k 0 := by
  induction v generalizing w k with
  | nil =>
    cases w with
    | nil => simp
    | cons y ys => simp at h
  | cons x xs ih =>
    cases w with
    | nil => simp at h
    | cons y ys =>
      have h' : xs.length = ys.length := by simpa using h
      cases k with
      | zero => simp
      | succ k => simpa using ih ys h' k

/-- `List.zipWith` of two maps over the *same* list is the map of the pointwise combination. -/
private theorem zipWith_map_map {α β γ : Type*} (op : β → β → γ) (f g : α → β) (l : List α) :
    List.zipWith op (l.map f) (l.map g) = l.map fun x => op (f x) (g x) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Row `i` of `m9vecZ` is additive: expanding the `k`-sum and distributing `a.getD _ 0`
over the sums `v.getD k 0 + w.getD k 0` (legitimate by `zipWith_getD_add`). -/
private theorem m9vecZ_row_add (a v w : List ℤ) (h : v.length = w.length) (i : ℕ) :
    ((List.range 3).map (fun k => a.getD (3 * i + k) 0 * (List.zipWith (· + ·) v w).getD k 0)).sum
      = ((List.range 3).map (fun k => a.getD (3 * i + k) 0 * v.getD k 0)).sum
        + ((List.range 3).map (fun k => a.getD (3 * i + k) 0 * w.getD k 0)).sum := by
  have hmap : (List.range 3).map (fun k => a.getD (3 * i + k) 0 * (List.zipWith (· + ·) v w).getD k 0)
      = (List.range 3).map
          (fun k => a.getD (3 * i + k) 0 * v.getD k 0 + a.getD (3 * i + k) 0 * w.getD k 0) :=
    List.map_congr_left fun k _ => by rw [zipWith_getD_add v w h k, mul_add]
  rw [hmap, List.sum_map_add]

theorem zassoc_m9vecZ_add (a v w : List ℤ) (h : v.length = w.length) :
    m9vecZ a (List.zipWith (· + ·) v w) = List.zipWith (· + ·) (m9vecZ a v) (m9vecZ a w) := by
  simp only [m9vecZ, zipWith_map_map]
  apply List.map_congr_left
  intro i _
  exact m9vecZ_row_add a v w h i

end Work.SG
