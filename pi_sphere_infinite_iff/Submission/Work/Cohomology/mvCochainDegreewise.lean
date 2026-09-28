import Mathlib
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.mvCochainF_injective
import Submission.Work.Cohomology.mvCochainG_surjective
import Submission.Work.Cohomology.mvCochainG_ker_le_range

/-!
# Degreewise short exactness of the cochain Mayer–Vietoris sequence

For subsets `U`, `V` of a topological space `X`, the cohomological Mayer–Vietoris sequence

`0 ⟶ C^*(C^{U,V}) --mvCochainF--> C^*(U) ⊞ C^*(V) --mvCochainG--> C^*(U ∩ V) ⟶ 0`

is obtained by dualising the (degreewise split) short exact sequence of *chain* complexes
`0 ⟶ C_*(U ∩ V) --mvLeft--> C_*(U) ⊞ C_*(V) --mvRight--> C^{U,V}_*(X) ⟶ 0`.

This file assembles the degreewise statement `mvCochainDegreewise` from the three ingredients,
proved in the sibling files:

* `mvCochainF_injective` — `mvCochainF.f n` is injective (the dual of the surjective `mvRight`);
* `mvCochainG_surjective` — `mvCochainG.f n` is surjective (the dual of the injective `mvLeft`);
* `mvCochainG_ker_le_range` — exactness in the middle (the dual of a short exact sequence of
  modules is exact in the middle).

Their conjunction, together with `mvCochainDegreeZero` (the composite is zero), is exactly the
`ShortExact`-ness of

`ShortComplex.mk (mvCochainF.f n) (mvCochainG.f n) (mvCochainDegreeZero U V n)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

/-- **The cochain Mayer–Vietoris sequence is short exact in every degree**: for all `n`, the
degree-`n` short complex of `ℤ`-modules
`C^n(C^{U,V}) --mvCochainF--> C^n(U) ⊞ C^n(V) --mvCochainG--> C^n(U ∩ V)`
is short exact. -/
theorem mvCochainDegreewise {X : TopCat} (U V : Set X) (n : ℕ) :
    (CategoryTheory.ShortComplex.mk ((Work.Cohomology.mvCochainF U V).f n)
      ((Work.Cohomology.mvCochainG U V).f n)
      (Work.Cohomology.mvCochainDegreeZero U V n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact mvCochainG_ker_le_range U V n hx₂
  · rw [ModuleCat.mono_iff_injective]
    exact mvCochainF_injective U V n
  · rw [ModuleCat.epi_iff_surjective]
    exact mvCochainG_surjective U V n

end Work.Cohomology
