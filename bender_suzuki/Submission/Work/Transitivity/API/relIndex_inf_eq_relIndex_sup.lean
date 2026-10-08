import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Transitivity.API

/-- For subgroups `A` and `K` of a group `G`, the relative index `K.relIndex A` equals the
cardinality of the image of `A` under the quotient map `G → G ⧸ K`.  This is the
orbit-stabilizer theorem applied to the action of `A` on the coset space `G ⧸ K`. -/
lemma relIndex_eq_card_image_mk {G : Type*} [Group G] (A K : Subgroup G) :
    K.relIndex A = Nat.card (QuotientGroup.mk '' (A : Set G) : Set (G ⧸ K)) := by
  have hstab : MulAction.stabilizer A (QuotientGroup.mk (1 : G) : G ⧸ K) = K.subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.subgroup_smul_def]
    change (QuotientGroup.mk ((a : G) * 1) : G ⧸ K) = QuotientGroup.mk (1 : G) ↔ (a : G) ∈ K
    rw [QuotientGroup.eq]
    simp
  have horb : MulAction.orbit A (QuotientGroup.mk (1 : G) : G ⧸ K)
      = (QuotientGroup.mk '' (A : Set G) : Set (G ⧸ K)) := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(a : G), a.2, by simp [MulAction.subgroup_smul_def]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, by simp [MulAction.subgroup_smul_def]⟩
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horb, ← Nat.card_coe_set_eq]

theorem relIndex_inf_eq_relIndex_sup {G : Type*} [Group G] [Finite G]
    {C J : Subgroup G} (h : ∀ z ∈ C ⊔ J, ∃ c ∈ C, ∃ j ∈ J, c * j = z) :
    (C ⊓ J).relIndex C = J.relIndex (C ⊔ J) := by
  -- Under the hypothesis, the quotient maps of `C` and of `C ⊔ J` onto `G ⧸ J` have the same
  -- image: every element of `C ⊔ J` is `c * j` with `c ∈ C`, and `c * j` and `c` lie in the same
  -- coset of `J`.
  have himage : (QuotientGroup.mk '' ((C ⊔ J : Subgroup G) : Set G) : Set (G ⧸ J))
      = QuotientGroup.mk '' (C : Set G) := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨c, hc, j, hj, hcj⟩ := h z hz
      refine ⟨c, hc, ?_⟩
      rw [← hcj, QuotientGroup.eq]
      simpa using hj
    · rintro y ⟨c, hc, rfl⟩
      exact ⟨c, Subgroup.mem_sup_left hc, rfl⟩
  calc
    (C ⊓ J).relIndex C = J.relIndex C := Subgroup.inf_relIndex_left C J
    _ = Nat.card (QuotientGroup.mk '' (C : Set G) : Set (G ⧸ J)) := relIndex_eq_card_image_mk C J
    _ = Nat.card (QuotientGroup.mk '' ((C ⊔ J : Subgroup G) : Set G) : Set (G ⧸ J)) :=
          by rw [← himage]
    _ = J.relIndex (C ⊔ J) := (relIndex_eq_card_image_mk (C ⊔ J) J).symm

end Work.Transitivity.API
