import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# Coefficient-function vocabulary for `Work.SG.RepCoh_ndvd`

`RC.linC rows cs q = ∑_{c < rows.length} cs.getD c 0 * rows_c[q]` is a list-indexed sum.
For the linear-combination argument in `RepCoh_ndvd` it is convenient to let the coefficient
list be an arbitrary function `ℕ → ℤ` (only the first `rows.length` values matter).  This file
introduces that mirror `LinF`, the bridge `linC_eq_LinF`, and elementary list facts about
`RC.vunit`.

Nothing here is `sorry`ed.
-/

namespace Work.SG

open Work.SG.RC

/-- The `q`-th coordinate of `∑_c f c • rowsₖ`, with the coefficient indexed by `ℕ`. -/
def LinF (rows : List (List ℤ)) (f : ℕ → ℤ) (q : ℕ) : ℤ :=
  ∑ c ∈ Finset.range rows.length, f c * (rows.getD c []).getD q 0

/-- `linC` is `LinF` for the coefficient function read off a list. -/
theorem linC_eq_LinF (rows : List (List ℤ)) (cs : List ℤ) (q : ℕ) :
    linC rows cs q = LinF rows (fun c => cs.getD c 0) q := by
  simp only [linC, LinF]
  rw [← List.sum_toFinset (fun c => cs.getD c 0 * (rows.getD c []).getD q 0) List.nodup_range,
    List.toFinset_range]

/-- `LinF` only reads its coefficient function on `[0, rows.length)`. -/
theorem LinF_congr (rows : List (List ℤ)) {f g : ℕ → ℤ}
    (h : ∀ c < rows.length, f c = g c) (q : ℕ) : LinF rows f q = LinF rows g q := by
  simp only [LinF]
  exact Finset.sum_congr rfl (fun c hc => by rw [h c (Finset.mem_range.mp hc)])

/-- The `c`-th entry of `(List.range M).map f` (for `c < M`). -/
theorem getD_map_range {M : ℕ} {f : ℕ → ℤ} {c : ℕ} (hc : c < M) :
    ((List.range M).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hc),
    List.getElem_map, List.getElem_range]

/-- The `r`-th coordinate of `RC.vunit k N q` for `r < N`. -/
theorem vunit_getD (k : ℤ) (N q r : ℕ) (hr : r < N) :
    (vunit k N q).getD r 0 = if r = q then k else 0 := by
  simp only [vunit]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hr),
    List.getElem_map, List.getElem_range]

end Work.SG
