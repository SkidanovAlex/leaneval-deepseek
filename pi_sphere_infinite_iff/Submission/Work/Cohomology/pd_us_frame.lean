import Mathlib
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.pd_union_aux

/-!
# A framing lemma for the descent to `U ∩ V`

`pd_us_mem_range_pdIncl_of_mem_range_pdTr` is a copy of the corresponding lemma of
`pd_glue3.lean` (that module clashes with `pd_relsub_aux`, which is imported elsewhere in the
development): a chain of `W` lying in the chains of the trace `pdTr W S` (for `S ⊆ W`) lifts to a
chain of `S`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-- **A chain of `W` lying in the chains of the trace `pdTr W S` lifts to a chain of `S`.** -/
theorem pd_us_mem_range_pdIncl_of_mem_range_pdTr {W S : Set M} (h : S ⊆ W) {n : ℕ}
    {y : (Work.Cohomology.singularChains ℤ (TopCat.of W)).X n}
    (hy : y ∈ LinearMap.range ((Work.Cohomology.inclChains (TopCat.of W)
      (Work.Cohomology.pdTr W S)).f n).hom) :
    y ∈ LinearMap.range ((Work.Cohomology.chainMap ℤ (TopCat.of S) (TopCat.of W)
      (Work.Cohomology.pdIncl W S h)).f n).hom := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(ModuleCat.Hom.hom ((Work.Cohomology.chainMap ℤ
    (TopCat.of (Work.Cohomology.pdTr W S)) (TopCat.of S)
    (Work.Cohomology.pdTrInv h)).f n)) z, ?_⟩
  have hkey : (ModuleCat.Hom.hom (((Work.Cohomology.chainMap ℤ
        (TopCat.of (Work.Cohomology.pdTr W S)) (TopCat.of S)
        (Work.Cohomology.pdTrInv h)) ≫ Work.Cohomology.inclChainsSub M S W h).f n)) z
      = (ModuleCat.Hom.hom ((Work.Cohomology.inclChains (TopCat.of W)
        (Work.Cohomology.pdTr W S)).f n)) z := by
    rw [← Work.Cohomology.inclChains_eq_pdTrInv (M := M) h]
  have hsub : Work.Cohomology.inclChainsSub M S W h
      = Work.Cohomology.chainMap ℤ (TopCat.of S) (TopCat.of W)
          (Work.Cohomology.pdIncl W S h) := rfl
  rw [hsub] at hkey
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hkey
  exact hkey

end

end Work.Cohomology
