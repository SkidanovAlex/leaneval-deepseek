import Submission.Work.Hering.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The subgroup `V = Inv(G) ∪ {1}`

For a group `G` of 2-rank `≥ 2` acting doubly transitively on its involutions, Peterfalvi I §2
p. 191 Step 1 shows that the involutions of `G` commute pairwise; hence `V = Inv(G) ∪ {1}` is an
elementary abelian normal subgroup of `G`. It is the starting point of the reduction
(`Work.Hering.Reduction`) and of the hard core (`Work.Hering.HardCore`).
-/

set_option autoImplicit false

namespace Work.Hering

open LeanEval.GroupTheory.Defs

variable {G : Type*} [Group G]

/-- `V = Inv(G) ∪ {1}`, a subgroup of `G` whenever `G` has 2-rank `≥ 2` and acts doubly
transitively on its involutions. -/
def invSubgroup (hDT : DTInv G) (h4 : HasFourGroup G) : Subgroup G where
  carrier := involutions G ∪ {1}
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_union, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | rfl
    · rcases hy with hy | rfl
      · by_cases hxy : x = y
        · exact Or.inr (by rw [hxy]; exact sq_eq_one_of_orderOf_eq_two hy)
        · exact Or.inl (mul_mem_involutions_of_dtinv hDT h4 hx hy hxy)
      · exact Or.inl (by simpa using hx)
    · rcases hy with hy | rfl
      · exact Or.inl (by simpa using hy)
      · exact Or.inr (by simp)
  one_mem' := by rw [Set.mem_union]; exact Or.inr rfl
  inv_mem' := by
    intro x hx
    rw [Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | rfl
    · exact Or.inl (involutions_inv_mem hx)
    · exact Or.inr (by simp)

theorem mem_invSubgroup (hDT : DTInv G) (h4 : HasFourGroup G) {x : G} :
    x ∈ invSubgroup hDT h4 ↔ orderOf x = 2 ∨ x = 1 := by
  have hmem : (x ∈ invSubgroup hDT h4) ↔ (x ∈ involutions G ∨ x = 1) := Iff.rfl
  rw [hmem]
  simp only [mem_involutions, Set.mem_singleton_iff, or_comm]

theorem involutions_subset_invSubgroup (hDT : DTInv G) (h4 : HasFourGroup G) :
    involutions G ⊆ (invSubgroup hDT h4 : Set G) := by
  intro x hx
  change x ∈ invSubgroup hDT h4
  rw [mem_invSubgroup]
  exact Or.inl hx

theorem involutions_eq_invSubgroup_diff (hDT : DTInv G) (h4 : HasFourGroup G) :
    involutions G = (invSubgroup hDT h4 : Set G) \ {1} := by
  ext x
  constructor
  · intro hx
    exact ⟨involutions_subset_invSubgroup hDT h4 hx, ne_one_of_mem_involutions hx⟩
  · intro ⟨hx, hx1⟩
    change x ∈ invSubgroup hDT h4 at hx
    rw [mem_invSubgroup] at hx
    rcases hx with hx | hx
    · exact hx
    · exact absurd hx hx1

theorem invSubgroup_normal (hDT : DTInv G) (h4 : HasFourGroup G) :
    (invSubgroup hDT h4).Normal where
  conj_mem := by
    intro n hn g
    rw [mem_invSubgroup] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (by rw [orderOf_conj]; exact hn)
    · exact Or.inr (by rw [hn]; simp)

theorem invSubgroup_comm (hDT : DTInv G) (h4 : HasFourGroup G) {x y : G}
    (hx : x ∈ invSubgroup hDT h4) (hy : y ∈ invSubgroup hDT h4) : x * y = y * x := by
  rw [mem_invSubgroup] at hx hy
  rcases hx with hx | rfl
  · rcases hy with hy | rfl
    · exact comm_of_dtinv hDT h4 x y hx hy
    · simp
  · simp

theorem pow_two_eq_one_of_mem_invSubgroup (hDT : DTInv G) (h4 : HasFourGroup G) {x : G}
    (hx : x ∈ invSubgroup hDT h4) : x * x = 1 := by
  rw [mem_invSubgroup] at hx
  rcases hx with hx | rfl
  · exact sq_eq_one_of_orderOf_eq_two hx
  · simp

theorem invSubgroup_le_centralizer (hDT : DTInv G) (h4 : HasFourGroup G) :
    invSubgroup hDT h4 ≤ Subgroup.centralizer ((invSubgroup hDT h4 : Set G)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact invSubgroup_comm hDT h4 hy hx

theorem isPGroup_invSubgroup (hDT : DTInv G) (h4 : HasFourGroup G) :
    IsPGroup 2 ↥(invSubgroup hDT h4) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  have h := pow_two_eq_one_of_mem_invSubgroup hDT h4 x.2
  have h2 : (x : G) ^ 2 = 1 := by simpa [pow_two] using h
  have h3 : orderOf (x : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hcoe : orderOf x = orderOf (x : G) :=
    (orderOf_injective (invSubgroup hDT h4).subtype (invSubgroup hDT h4).subtype_injective x).symm
  rcases Nat.dvd_prime Nat.prime_two |>.mp h3 with h3' | h3'
  · exact ⟨0, by rw [hcoe, h3']; norm_num⟩
  · exact ⟨1, by rw [hcoe, h3']; norm_num⟩

end Work.Hering
