/-
  WilG4c — the "thick base" step of the cell section (BNZ §2.2/§2.3).

  A cell `Z ⊆ ℝ^{m+1}` with empty interior whose projection to the first `m` coordinates has
  nonempty interior must be a *graph* cell: a band cell over a base with interior would itself
  have interior (`Work.WilG1.Cell.interior_band_nonempty`, via
  `band_no_interior_projLast`).  Once `Z` is the graph of a function `f` over a set `C`, every
  vertical fibre of `Z` is a singleton or empty, so `loOf m Z` is exactly `f` (and `0` off `C`),
  which gives

  * `graphOf (loOf m Z) = A_lo m Z` (the `A_lo` description is the first-order graph of the
    pointwise infimum, and a singleton fibre has its own element as infimum), and
  * every point of `Z` lies on that graph.

  The two halves are `graphOf_loOf_eq_of_graph` (the graph-cell analysis) and
  `band_no_interior_projLast` (the elimination of the band case); this file is the assembly.
-/
import Mathlib
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.FiberEndsLo
import Submission.Work.WilG4c.band_no_interior_projLast
import Submission.Work.WilG4c.graphOf_loOf_eq_of_graph

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

theorem thickBase_loOf {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    (hcell : WilkiesDesign.IsCell (m + 1) Z) (hInt : interior Z = ∅)
    (hne : (interior (WilkiesDesign.projLast Z)).Nonempty) :
    WilkiesDesign.graphOf (Work.WilG4c.loOf m Z) = Work.WilG4c.A_lo m Z ∧
      ∀ l ∈ Z, ∃ μ : Fin m → ℝ, Fin.snoc μ (Work.WilG4c.loOf m Z μ) = l := by
  rcases Work.WilG1.Cell.cell_cases hcell with
    ⟨C, f, _hf, hmem⟩ | ⟨C, a, b, ha, hb, hab, hmem⟩
  · exact graphOf_loOf_eq_of_graph hmem
  · exact absurd hne (band_no_interior_projLast ha hb hab hmem hInt)

end Work.WilG4c
