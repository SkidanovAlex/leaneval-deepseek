import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace Commons.MeasureTheory.Measurable

/-- The union of any family of nondegenerate closed intervals of `ℝ` is measurable:
it is a countable union of connected components, each of which is an interval. -/
theorem union_Icc_measurable (C : Set (ℝ × ℝ)) (hC : ∀ p ∈ C, p.1 < p.2) :
    MeasurableSet (⋃ p ∈ C, Set.Icc p.1 p.2) := by
  set U : Set ℝ := ⋃ p ∈ C, Set.Icc p.1 p.2 with hU
  have hcover : U = ⋃ q : ℚ, connectedComponentIn U (q : ℝ) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [hU, Set.mem_iUnion] at hx
      obtain ⟨p, hxp⟩ := hx
      rw [Set.mem_iUnion] at hxp
      obtain ⟨hpC, hxp⟩ := hxp
      rw [Set.mem_Icc] at hxp
      have hab : p.1 < p.2 := hC p hpC
      have hsub : Set.Icc p.1 p.2 ⊆ U := by
        intro y hy
        rw [hU]
        exact Set.mem_biUnion hpC hy
      obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn hab
      refine Set.mem_iUnion.mpr ⟨q, ?_⟩
      exact isPreconnected_Icc.subset_connectedComponentIn ⟨hq_lo.le, hq_hi.le⟩ hsub hxp
    · intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨q, hxq⟩ := hx
      exact connectedComponentIn_subset U (q : ℝ) hxq
  rw [hcover]
  exact MeasurableSet.iUnion (fun q : ℚ => isPreconnected_connectedComponentIn.measurableSet)

end Commons.MeasureTheory.Measurable