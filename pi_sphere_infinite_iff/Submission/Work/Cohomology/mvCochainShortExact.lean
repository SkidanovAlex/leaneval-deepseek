import Mathlib
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.mvCochainF_injective
import Submission.Work.Cohomology.mvCochainG_surjective
import Submission.Work.Cohomology.mvCochainG_ker_le_range

namespace Work.Cohomology

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

/-- **The Mayer–Vietoris short exact sequence of cochain complexes.**

For subsets `U`, `V` of a topological space `X` there are maps

`C^*(C^{U,V}) --f--> C^*(U) ⊞ C^*(V) --g--> C^*(U ∩ V)`

(f the dual of `(smallOfU, -smallOfV)` and g the dual of `(inclUVU_*, inclUVV_*)`) whose
composite is zero and which form a short exact sequence of cochain complexes.

The proof is degreewise: at each degree `n` the sequence of `ℤ`-modules
`C^n(C^{U,V}) ⟶ C^n(U) ⊞ C^n(V) ⟶ C^n(U ∩ V)` is short exact, because the degree-`n` sequence
of the Mayer–Vietoris sequence of chain complexes (`mv_shortExact`) is short exact and every
degree of the small chains is a free `ℤ`-module (`smallChains U V` is the simplicial chain
complex of a simplicial set), so that `Hom(-,ℤ)` preserves its exactness.  The three degreewise
statements are `mvCochainF_injective` (left exactness of `Hom(-,ℤ)` applied to the surjection
`mvRight`), `mvCochainG_ker_le_range` (left exactness applied to `im mvLeft = ker mvRight`) and
`mvCochainG_surjective` (the dual of the split inclusion `mvLeft`). -/
theorem mvCochainShortExact {X : TopCat} (U V : Set X) :
    ∃ (f : Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallChains U V) ⟶
        CategoryTheory.Limits.biprod (Work.Cohomology.singularCochainComplex ℤ (TopCat.of U))
          (Work.Cohomology.singularCochainComplex ℤ (TopCat.of V)))
      (g : CategoryTheory.Limits.biprod (Work.Cohomology.singularCochainComplex ℤ (TopCat.of U))
          (Work.Cohomology.singularCochainComplex ℤ (TopCat.of V)) ⟶
        Work.Cohomology.singularCochainComplex ℤ (TopCat.of ↥(U ∩ V)))
      (w : CategoryTheory.CategoryStruct.comp f g = 0),
      (CategoryTheory.ShortComplex.mk f g w).ShortExact := by
  refine ⟨mvCochainF U V, mvCochainG U V, mvCochainComp U V, ?_⟩
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
    exact mvCochainG_ker_le_range U V n
  · rw [ModuleCat.mono_iff_injective]
    exact mvCochainF_injective U V n
  · rw [ModuleCat.epi_iff_surjective]
    exact mvCochainG_surjective U V n

end Work.Cohomology
