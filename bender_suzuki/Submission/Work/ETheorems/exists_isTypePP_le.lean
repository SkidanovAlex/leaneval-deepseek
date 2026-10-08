import Mathlib
import Submission.Work.ETheorems.Defs
import Submission.Work.LocalPrelim.card_omega_one_eq_pow_rank
import Submission.Work.PGroup.two_index_prime_subgroups

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A non-cyclic commutative `p`-subgroup contains a subgroup of type `(p,p)`

If `C` is a finite commutative `p`-subgroup of a group `G` which is **not** cyclic, then `C`
contains an elementary abelian subgroup `B` of order `p ^ 2`, i.e. a subgroup of FT-type `(p,p)`.

The proof is the standard `Ω₁`-argument.  Since `C` is not cyclic its minimal number of
generators is at least `2` (`Work.PGroup.isCyclic_of_rank_le_one`), so
`Ω₁(C)` is elementary abelian of order `p ^ Group.rank C ≥ p ^ 2`
(`Work.LocalPrelim.card_omega_one_eq_pow_rank`), and Sylow's first theorem produces a subgroup
of `Ω₁(C)` of order exactly `p ^ 2`.  As a subgroup of an elementary abelian group it is itself
elementary abelian.
-/

set_option linter.unusedVariables false

namespace Work.ETheorems

/-- If `A` is a finite commutative `p`-subgroup of `G` with `Group.rank A ≥ 2`, then `A`
contains an elementary abelian subgroup of order `p ^ 2`. -/
theorem exists_elementaryAbelian_card_prime_sq_of_rank_two {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hAc : IsMulCommutative ↥A) (hAp : IsPGroup p A)
    (hrank : 2 ≤ Group.rank ↥A) :
    ∃ E : Subgroup G, E ≤ A ∧ Work.PGroup.IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  -- `Ω₁(A)` is elementary abelian and has order `p ^ Group.rank A ≥ p ^ 2`.
  set Ω : Subgroup G := Work.PGroup.omega p 1 A with hΩdef
  have hΩle : Ω ≤ A := Work.PGroup.omega_le p 1 A
  have hΩel : Work.PGroup.IsElementaryAbelian p Ω := by
    rw [hΩdef, Work.PGroup.omega_one_eq_omega1]
    exact ⟨Work.PGroup.omega1_isMulCommutative hAc,
      fun x => Subtype.ext (by simpa using Work.PGroup.omega1_pow_eq_one hAc x.2)⟩
  have hΩcard : Nat.card ↥Ω = p ^ Group.rank ↥A :=
    Work.LocalPrelim.card_omega_one_eq_pow_rank hp hAc hAp
  have hle : p ^ 2 ≤ Nat.card ↥Ω := by
    rw [hΩcard]
    exact Nat.pow_le_pow_right hp.pos hrank
  -- Sylow's first theorem gives a subgroup of `Ω₁(A)` of order `p ^ 2`.
  obtain ⟨H, -, hHcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp hΩel.isPGroup (H := ⊤)
      (by simpa using hle)
  refine ⟨H.map Ω.subtype, (Subgroup.map_subtype_le H).trans hΩle, ?_, ?_⟩
  · exact hΩel.mono (Subgroup.map_subtype_le H)
  · rw [Subgroup.card_map_of_injective Ω.subtype_injective, hHcard]

theorem exists_isTypePP_le {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {C : Subgroup G} (hC : IsPGroup p C) (hab : IsMulCommutative ↥C) (hnc : ¬ IsCyclic ↥C) :
    ∃ B : Subgroup G, B ≤ C ∧ Work.LocalPrelim.IsTypePP p B := by
  -- A non-cyclic group needs at least two generators.
  have hrank : 2 ≤ Group.rank ↥C := by
    by_contra h
    exact hnc (Work.PGroup.isCyclic_of_rank_le_one (G := ↥C) (by omega))
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    exists_elementaryAbelian_card_prime_sq_of_rank_two hp hab hC hrank
  exact ⟨E, hE, hEel, hEcard⟩

end Work.ETheorems
