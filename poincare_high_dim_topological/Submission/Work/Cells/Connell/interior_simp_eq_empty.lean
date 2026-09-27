import Mathlib
import Submission.Work.PL.Defs

/-!
# The simplex on at most `n` vertices in `ℝⁿ` has empty interior

`PL.simp s` is the convex hull of a finite vertex set `s` in `PL.E n = ℝⁿ`.  Its affine span
has the same dimension as the vector span of the differences of the vertices of `s`, hence at
most `s.card - 1`; for `s.card ≤ n` this is strictly smaller than `n`, so the simplex lies in a
proper affine subspace of `ℝⁿ` and therefore has empty interior.

The two Mathlib inputs are
* `affineSpan_image_ne_top_of_encard_le_finrank`: the affine span of a finite set of at most
  `finrank` points is proper, and
* `interior_convexHull_nonempty_iff_affineSpan_eq_top`: a convex hull in finite dimension has
  nonempty interior exactly when its affine span is everything.
-/

open Set Metric

namespace Work.Cells.Connell

theorem interior_simp_eq_empty {n : ℕ} (s : Finset (PL.E n)) (h : s.card ≤ n) :
    interior (PL.simp s) = ∅ := by
  rw [PL.simp, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top] at hne
  refine (affineSpan_image_ne_top_of_encard_le_finrank ℝ (Finset.finite_toSet s) ?_ id) ?_
  · rw [Set.encard_coe_eq_coe_finsetCard, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast h
  · simpa using hne

end Work.Cells.Connell
