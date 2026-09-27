import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic

/-!
# `PL/Generic/Hull`: `hullOf`, the convex hull of the image of an index set

`hullOf y s = convexHull ℝ (y '' s)` is the vertex-map form of `PL.simp`: the simplex spanned by the
images of the indices in `s`.  This is the vocabulary of `Work.PL.Generic.gp_pairs` (G6a′, the
corrected general position statement of `Submission/Work/NOTES_LEAD_poincare_engulf.md` §4.1).
-/

open Set Metric PL

namespace Work.PL.Generic

variable {n : ℕ} {ι : Type*}

/-- Convex hull of the image of a finite index set under a vertex map. -/
def hullOf (y : ι → E n) (s : Finset ι) : Set (E n) := convexHull ℝ (y '' (s : Set ι))

@[simp] theorem hullOf_empty (y : ι → E n) : hullOf y ∅ = ∅ := by
  simp [hullOf]

@[simp] theorem hullOf_singleton (y : ι → E n) (i : ι) : hullOf y {i} = {y i} := by
  simp [hullOf]

theorem hullOf_eq_simp (y : ι → E n) (s : Finset ι) : hullOf y s = PL.simp (s.image y) := by
  rw [hullOf, PL.simp, Finset.coe_image]

theorem hullOf_mono {y : ι → E n} {s t : Finset ι} (h : s ⊆ t) : hullOf y s ⊆ hullOf y t := by
  rw [hullOf_eq_simp, hullOf_eq_simp]
  exact PL.simp_mono (Finset.image_subset_image h)

theorem convex_hullOf (y : ι → E n) (s : Finset ι) : Convex ℝ (hullOf y s) :=
  convex_convexHull ℝ _

theorem isCompact_hullOf (y : ι → E n) (s : Finset ι) : IsCompact (hullOf y s) :=
  (s.finite_toSet.image y).isCompact_convexHull ℝ

theorem isBounded_hullOf (y : ι → E n) (s : Finset ι) : Bornology.IsBounded (hullOf y s) :=
  (isCompact_hullOf y s).isBounded

theorem hullOf_subset_affineSpan (y : ι → E n) (s : Finset ι) :
    hullOf y s ⊆ (affineSpan ℝ (y '' (s : Set ι)) : Set (E n)) :=
  convexHull_min (subset_affineSpan ℝ _) (AffineSubspace.convex _)

end Work.PL.Generic
