import Mathlib
import Submission.Work.Hering.Step3.NormalizerQuotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `fixedToQuot` preserves commutativity

Let `s, t ∈ Inv(G)` be involutions fixed by the subgroup `P`.  Then both `s` and `t` lie in
`C_G(P) ≤ N_G(P)`, so both have a class in `N_G(P)/P`.  This file shows that if `s` and `t`
commute in `G`, then their classes in `N_G(P)/P` commute as well.

Indeed, `fixedToQuot P s hs` is the image of the element `s ∈ N_G(P)` under the natural map
`N_G(P) → N_G(P)/P`, and similarly for `t`.  Since `s` and `t` commute in `G`, they commute as
elements of the subgroup `N_G(P)`, and any homomorphism preserves commutativity.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Hering.Step3

open Work.Hering

/-- The images under the quotient map `N_G(P) → N_G(P)/P` of two commuting elements commute. -/
theorem fixedToQuot_mk'_mul_comm {G : Type*} [Group G] (P : Subgroup G)
    (gs gt : ↥(Subgroup.normalizer (P : Set G))) (h : gs * gt = gt * gs) :
    QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) gs *
        QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) gt =
      QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) gt *
        QuotientGroup.mk' (P.subgroupOf (Subgroup.normalizer (P : Set G))) gs := by
  rw [← map_mul, ← map_mul, h]

/-- If two `P`-fixed involutions commute in `G`, their classes in `N_G(P)/P` commute. -/
theorem fixedToQuot_mul_comm {G : Type*} [Group G] {P : Subgroup G}
    {s t : {x : G // x ∈ involutions G}} (hs : s ∈ involutionsFixedBy P)
    (ht : t ∈ involutionsFixedBy P) (hst : (s : G) * (t : G) = (t : G) * (s : G)) :
    fixedToQuot P s hs * fixedToQuot P t ht = fixedToQuot P t ht * fixedToQuot P s hs := by
  let gs : ↥(Subgroup.normalizer (P : Set G)) :=
    ⟨(s : G), mem_normalizer_of_mem_involutionsFixedBy hs⟩
  let gt : ↥(Subgroup.normalizer (P : Set G)) :=
    ⟨(t : G), mem_normalizer_of_mem_involutionsFixedBy ht⟩
  have hfqs : fixedToQuot P s hs = QuotientGroup.mk' _ gs := rfl
  have hfqt : fixedToQuot P t ht = QuotientGroup.mk' _ gt := rfl
  have hcomm : gs * gt = gt * gs := by
    apply Subtype.ext
    show (gs : G) * (gt : G) = (gt : G) * (gs : G)
    simpa using hst
  rw [hfqs, hfqt]
  exact fixedToQuot_mk'_mul_comm P gs gt hcomm

end Work.Hering.Step3
