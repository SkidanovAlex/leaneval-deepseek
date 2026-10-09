import Mathlib
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.KrullCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for `br_pTorsion_openSubgroup`

This file fixes the definition used by the proof that the `p`-torsion of the local Brauer group
`H²(U, Ωˣ)` at an **arbitrary open** subgroup `U ≤ D_A = decomp k A` has exactly `p` elements
(`Work.SSGRoute.PT.br_pTorsion_openSubgroup_v2`).

The mathematical point of the reduction: an open subgroup `U ≤ D_A` is exactly the decomposition
group *at the level of a finite subextension of `Ω`*.  Concretely, for every open `U` there is a
finite extension `L/k` inside `Ω` with

  `U = {x ∈ D_A : x fixes L pointwise}`        (`levelFixSub`),

and then the theorem is the statement `Work.SSGRoute.Nakayama.br_pTorsion` for the *number field*
`↥L` (with the same algebraic closure `Ω` and the same place `A`), transported across the
homeomorphism `decomp ↥L A ≃* U` (`exists_homeomorph_decompLevelEquiv`).
-/

namespace Work.SSGRoute.PT

/-- **The subgroup of `D_A` fixing a finite level `L` pointwise**: the group of elements of the
decomposition group `D_A = SSGRoute.decomp k A` of the finite place `A` whose underlying
`k`-automorphism of `Ω` fixes the intermediate field `L` pointwise.

For `L/k` finite this is an *open* subgroup of `D_A`, and every open subgroup of `D_A` is of this
form (`Work.SSGRoute.PT.openSubgroup_eq_levelFixSub`). -/
def levelFixSub (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω)
    (L : IntermediateField k Ω) : Subgroup ↥(SSGRoute.decomp k A) :=
  (L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)

theorem levelFixSub_eq_comap (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (L : IntermediateField k Ω) :
    levelFixSub k Ω A L = (L.fixingSubgroup ⊓ SSGRoute.decomp k A).comap
      (SSGRoute.decomp k A).subtype := by
  ext x
  rw [levelFixSub, Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

@[simp] theorem mem_levelFixSub {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {A : ValuationSubring Ω} {L : IntermediateField k Ω} {x : ↥(SSGRoute.decomp k A)} :
    x ∈ levelFixSub k Ω A L ↔ ∀ y ∈ L, (x : Ω ≃ₐ[k] Ω) y = y := by
  rw [levelFixSub, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]

end Work.SSGRoute.PT
