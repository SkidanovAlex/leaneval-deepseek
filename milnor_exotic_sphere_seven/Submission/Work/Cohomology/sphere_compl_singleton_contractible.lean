import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sphere minus a point is contractible

For a real inner product space `E` and a point `c` of the unit sphere of `E`, the complement of
`{c}` in the unit sphere is contractible.

The proof is geometric: stereographic projection centred at `c`,
`stereographic (norm_eq_of_mem_sphere c)`, is an open partial homeomorphism from the unit
sphere onto the orthogonal complement `(ℝ ∙ c)ᗮ`, whose source is exactly `{c}ᶜ` and whose target is
everything.  Hence the punctured sphere is homeomorphic to `(ℝ ∙ c)ᗮ`, a real topological vector
space and therefore contractible (`RealTopologicalVectorSpace.contractibleSpace`).
-/

namespace Work.Cohomology

open Metric

theorem sphere_compl_singleton_contractible (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : Metric.sphere (0 : E) 1) : ContractibleSpace {y : Metric.sphere (0 : E) 1 // y ≠ c} := by
  -- Stereographic projection centred at `c`, as an open partial homeomorphism from the unit
  -- sphere onto the orthogonal complement of `c`; its source is the complement of `{c}`.
  have hsrc : (stereographic (v := (c : E)) (norm_eq_of_mem_sphere c)).source
      = {y : Metric.sphere (0 : E) 1 | y ≠ c} := by
    simp only [stereographic_source]
    ext y
    simp
  have htrg : (stereographic (v := (c : E)) (norm_eq_of_mem_sphere c)).target
      = Set.univ :=
    stereographic_target _
  -- so the punctured sphere is homeomorphic to `(ℝ ∙ c)ᗮ`
  have e : {y : Metric.sphere (0 : E) 1 // y ≠ c} ≃ₜ (ℝ ∙ (c : E))ᗮ :=
    (((Homeomorph.setCongr hsrc).symm.trans
        (OpenPartialHomeomorph.toHomeomorphSourceTarget _)).trans
      (Homeomorph.setCongr htrg)).trans (Homeomorph.Set.univ _)
  -- which is a real topological vector space, hence contractible
  exact e.contractibleSpace

end Work.Cohomology
