import Mathlib
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.cap_mem_range_inclChains

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology
noncomputable section

theorem pd_inter_lift {M : TopCat} {U V : Set M} {k mj : ℕ}
    (χ : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) k)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X (k + (mj + 1)))
    (hα₂ : α₂ ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdTr (U ∪ V) (U ∩ V))).f (k + (mj + 1))).hom) :
    ∃ y : (singularChains ℤ (TopCat.of ↥(U ∩ V))).X (mj + 1),
      (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥(U ∪ V))
        (pdIncl (U ∪ V) (U ∩ V)
          (Set.inter_subset_left.trans Set.subset_union_left))).f (mj + 1) y
        = cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂ := by
  have h1 : cap ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) χ (mj + 1) α₂
      ∈ LinearMap.range ((inclChains (TopCat.of ↥(U ∪ V))
          (pdTr (U ∪ V) (U ∩ V))).f (mj + 1)).hom :=
    cap_mem_range_inclChains (M := TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V))
      k (mj + 1) χ hα₂
  have h2 := mem_range_pdIncl_of_mem_range_pdTr (M := M) (W := U ∪ V) (S := U ∩ V)
    (Set.inter_subset_left.trans Set.subset_union_left) (n := mj + 1) h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

end
end Work.Cohomology
