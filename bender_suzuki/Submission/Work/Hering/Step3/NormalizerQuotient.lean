import Mathlib
import Submission.Work.Hering.Step3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The quotient `N_G(P)/P`

For the proof that `C_G(U)` is a `2`-group (Peterfalvi I §2 Step 3) one applies the minimality
hypothesis (E2) to the quotient `N_G(P)/P`, where `P` is an odd `p`-subgroup of `C_G(U)`.  This
file provides the quotient `N_G(P)/P` -- in particular the (`instance`-level) normality of `P` in
its normaliser -- and the natural map sending a `P`-fixed involution `s ∈ V` to its class in
`N_G(P)/P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Hering.Step3

open LeanEval.GroupTheory.Defs
open Work.Hering

/-- `P` is normal in its own normaliser (the normaliser is self-normalising), so that the quotient
`N_G(P)/P` is a group. -/
instance instNormalSubgroupOfNormalizer {G : Type*} [Group G] (P : Subgroup G) :
    (P.subgroupOf (Subgroup.normalizer (P : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (H := P)
      (K := Subgroup.normalizer (P : Set G)) (Subgroup.le_normalizer (H := P))).mpr le_rfl

/-- The class in `N_G(P)/P` of an involution `s` fixed by `P` (so that `s ∈ C_G(P) ≤ N_G(P)`). -/
def fixedToQuot {G : Type*} [Group G] (P : Subgroup G)
    (s : {x : G // x ∈ involutions G}) (hs : s ∈ involutionsFixedBy P) :
    ↥(Subgroup.normalizer (P : Set G)) ⧸ P.subgroupOf (Subgroup.normalizer (P : Set G)) :=
  QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G)))
    ⟨(s : G), mem_normalizer_of_mem_involutionsFixedBy hs⟩

end Work.Hering.Step3
