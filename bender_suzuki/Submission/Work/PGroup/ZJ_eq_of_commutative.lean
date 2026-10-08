import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `ZJ(P) = P` for a commutative `P`

`ZJ P = Z(J(P))` is the center of the Thompson subgroup of `P`.  If `P` is commutative then
`J(P) = P` (the subgroup `P` is itself an abelian subgroup of `P` of maximal possible order) and
`Z(P) = P`, so `ZJ P = P`.

The helper lemmas are `private` so that they cannot clash with the (identically named, but
elsewhere located) statements proved by colleagues about the Thompson subgroup.
-/

namespace Work.PGroup

/-- If `P` is commutative then the maximal order of an abelian subgroup of `P` is `|P|` itself:
`P` is an abelian subgroup of `P`, and every subgroup of `P` has cardinality at most `|P|`. -/
private lemma maxAbelianOrder_eq_card_of_commutative {G : Type*} [Group G] (P : Subgroup G)
    [Finite P] (hP : IsMulCommutative P) : maxAbelianOrder P = Nat.card P := by
  rw [maxAbelianOrder]
  set S : Set ℕ := {n | ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = n} with hS
  have hmem : Nat.card P ∈ S := ⟨P, le_rfl, hP, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hle : ∀ b ∈ S, b ≤ Nat.card P := by
    rintro n ⟨A, hA, -, rfl⟩
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  have hbdd : BddAbove S := ⟨Nat.card P, hle⟩
  exact le_antisymm (csSup_le hne hle) (le_csSup hbdd hmem)

/-- If `P` is commutative then `P` itself is an abelian subgroup of `P` of maximal order,
hence generates the Thompson subgroup: `J(P) = P`. -/
private lemma thompsonJ_eq_self_of_commutative {G : Type*} [Group G] (P : Subgroup G)
    [Finite P] (hP : IsMulCommutative P) : thompsonJ P = P := by
  refine le_antisymm (thompsonJ_le P) ?_
  exact le_thompsonJ le_rfl hP (maxAbelianOrder_eq_card_of_commutative P hP).symm

/-- The center of a commutative subgroup, as a subgroup of the ambient group, is the subgroup
itself. -/
private lemma centerIn_eq_self_of_commutative {G : Type*} [Group G] (P : Subgroup G)
    (hP : IsMulCommutative P) : centerIn P = P := by
  rw [centerIn, Subgroup.center_eq_top (hG := hP), Subgroup.map_top]
  exact Subgroup.range_subtype P

theorem ZJ_eq_of_commutative {G : Type*} [Group G] (P : Subgroup G) [Finite P]
    (hP : IsMulCommutative P) : Work.PGroup.ZJ P = P := by
  rw [ZJ, thompsonJ_eq_self_of_commutative P hP]
  exact centerIn_eq_self_of_commutative P hP

end Work.PGroup
