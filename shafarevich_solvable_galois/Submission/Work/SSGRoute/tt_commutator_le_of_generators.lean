import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped commutatorElement

set_option linter.unusedVariables false

/-- If a set `S` generates a group `Q` and the commutator of any two generators lies in a
normal subgroup `N`, then `N` contains the full commutator subgroup of `Q`.  (The centrality
hypothesis on `N` is not needed for this direction.) -/
theorem tt_commutator_le_of_generators {Q : Type*} [Group Q] (S : Set Q)
    (hS : Subgroup.closure S = ⊤) (N : Subgroup Q) [N.Normal] (hN : N ≤ Subgroup.center Q)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ N) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ N := by
  -- The image of `S` in `Q ⧸ N` still generates the quotient and consists of pairwise
  -- commuting elements, so the quotient is abelian.
  have htop : Subgroup.closure ((QuotientGroup.mk' N) '' S) = ⊤ := by
    rw [← MonoidHom.map_closure (QuotientGroup.mk' N) S, hS,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hcommq : ∀ x ∈ (QuotientGroup.mk' N) '' S, ∀ y ∈ (QuotientGroup.mk' N) '' S,
      x * y = y * x := by
    rintro x ⟨s, hs, rfl⟩ y ⟨s', hs', rfl⟩
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement (QuotientGroup.mk' N),
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcomm s hs s' hs'
  have hKc : IsMulCommutative (Subgroup.closure ((QuotientGroup.mk' N) '' S)) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcommq x hx y hy)
  have hqcomm : IsMulCommutative (Q ⧸ N) := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    have ha : a ∈ Subgroup.closure ((QuotientGroup.mk' N) '' S) := by
      rw [htop]; exact Subgroup.mem_top a
    have hb : b ∈ Subgroup.closure ((QuotientGroup.mk' N) '' S) := by
      rw [htop]; exact Subgroup.mem_top b
    exact Subtype.ext_iff.mp (hKc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hqcomm

end Work.SSGRoute
