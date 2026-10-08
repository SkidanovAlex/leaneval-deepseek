import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.thompsonJ_characteristic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N_G(P) ≤ N_G(J(P))`

The Thompson subgroup `J(P)` is characteristic in `P`
(`Work.PGroup.thompsonJ_characteristic`), so every element of the normalizer of `P` lies in the
normalizer of `J(P)`.  This is the formal content of the phrase "the Thompson subgroup is
characteristic in `P`" used in the Feit–Thompson development.
-/

open scoped Classical Pointwise
open Subgroup

noncomputable section

namespace Work.PGroup

theorem thompsonJ_le_normalizer {G : Type*} [Group G] (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Work.PGroup.thompsonJ P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h := thompsonJ_characteristic P g hg
  rw [conjBy, Subgroup.pointwise_smul_def] at h
  exact h

end Work.PGroup
