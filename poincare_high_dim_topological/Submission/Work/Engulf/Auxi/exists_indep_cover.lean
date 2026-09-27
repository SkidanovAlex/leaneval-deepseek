import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.Auxi

open Set

/-- Every point of the simplex on a finite vertex set `s ⊆ ℝⁿ` lies in the simplex on an affinely
independent, nonempty subset of `s`.  This is Carathéodory's convexity result in its "affinely
independent" form, specialised to a finite vertex set, so no dimension hypothesis is needed: a point
of `PL.simp s = convexHull ℝ ↑s` is in the convex hull of a minimal-cardinality subset of `s`, which
is affinely independent.  Suggested proof: `rw [PL.simp, convexHull_eq_union] at hy` (Mathlib,
`Mathlib/Analysis/Convex/Caratheodory.lean`), then unwrap the `iUnion`/`exists_prop`; nonemptiness
of the subset follows from `convexHull_nonempty_iff` and `Finset.coe_nonempty`. -/
theorem exists_indep_cover {n : ℕ} (s : Finset (PL.E n)) {y : PL.E n} (hy : y ∈ PL.simp s) :
    ∃ t : Finset (PL.E n), t ⊆ s ∧ t.Nonempty ∧
      AffineIndependent ℝ (fun v : ↥t => (v : PL.E n)) ∧ y ∈ PL.simp t := by
  rw [PL.simp, convexHull_eq_union] at hy
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨t, hts, haff, hyt⟩ := hy
  refine ⟨t, ?_, ?_, haff, ?_⟩
  · exact Finset.coe_subset.mp hts
  · rw [← Finset.coe_nonempty]
    exact (convexHull_nonempty_iff (𝕜 := ℝ)).mp ⟨y, hyt⟩
  · simpa [PL.simp] using hyt

end Work.Engulf.Auxi
