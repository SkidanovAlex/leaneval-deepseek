import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PGroup

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- The image of an elementary abelian `p`-subgroup of `G` under an injective homomorphism
`f : G →* N` is again elementary abelian of exponent `p`. -/
theorem isElementaryAbelian_map {N : Type*} [Group N] {f : G →* N} (hf : Function.Injective f)
    {E : Subgroup G} (hE : IsElementaryAbelian p E) : IsElementaryAbelian p (E.map f) := by
  have e := E.equivMapOfInjective f hf
  constructor
  · rw [isMulCommutative_iff]
    intro x y
    refine e.symm.injective ?_
    simp only [map_mul]
    exact hE.mul_comm (e.symm x) (e.symm y)
  · intro x
    rw [← e.apply_symm_apply x, ← map_pow, hE.pow_eq_one, map_one]

/-- The minimal number of generators of a subgroup of a finite group is bounded by the order of
the ambient group. -/
theorem rank_le_card (E : Subgroup G) [Finite G] : Group.rank ↥E ≤ Nat.card G := by
  haveI : Fintype ↥E := Fintype.ofFinite _
  calc Group.rank ↥E ≤ (Finset.univ : Finset ↥E).card :=
        Group.rank_le (S := Finset.univ) (by rw [Finset.coe_univ, Subgroup.closure_univ])
    _ = Nat.card ↥E := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ Nat.card G := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- The `p`-rank is monotone with respect to taking subgroups: every elementary abelian
`p`-subgroup of `H ≤ G` is (up to the inclusion) an elementary abelian `p`-subgroup of `G`, and
`Group.rank` is preserved by the resulting isomorphism. -/
theorem mRank_mono {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) [Finite G] :
    Work.PGroup.mRank p H ≤ Work.PGroup.mRank p G := by
  have hbdd : BddAbove {n : ℕ | ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Group.rank E = n} :=
    ⟨Nat.card G, by rintro n ⟨E, -, rfl⟩; exact rank_le_card E⟩
  have hne : ({n : ℕ | ∃ E : Subgroup ↥H, IsElementaryAbelian p E ∧ Group.rank E = n}).Nonempty :=
    ⟨Group.rank (⊥ : Subgroup ↥H), ⊥, isElementaryAbelian_bot p, rfl⟩
  have hsub : {n : ℕ | ∃ E : Subgroup ↥H, IsElementaryAbelian p E ∧ Group.rank E = n} ⊆
      {n : ℕ | ∃ E : Subgroup G, IsElementaryAbelian p E ∧ Group.rank E = n} := by
    rintro n ⟨E, hE, hrank⟩
    refine ⟨E.map H.subtype, isElementaryAbelian_map H.subtype_injective hE, ?_⟩
    rw [← hrank, (Group.rank_congr (E.equivMapOfInjective H.subtype H.subtype_injective)).symm]
  simpa only [mRank] using csSup_le_csSup hbdd hne hsub

end Work.PGroup
